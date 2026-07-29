#!/usr/bin/env python3
"""
m0.py — hostile independent executor / differential witness for the M₀
Lean mechanization (Lemma4.lean).

STATUS (fixed by review, 2026-07-09):
    Lean   : theorems (SoundSubstrate laws, substrate independence).
    m0.py  : falsification / validation witness.  Agreement on millions
             of cases raises confidence; a discrepancy is a counter-
             example to the *implementation or the specification
             transcription* — never to the theorem.

Phases (reviewer's fixed development order):
    A  AST generator + pure sequential evaluator,
       differential check: python_seq == Lean #eval (runSeq).
    B  parallel trace generator (attempt / snapshot / abort / commit)
       and wavefront generator; checks per trace:
           forced     : proj(trace) == J
           sound      : result(trace) == Seq(P,J)
           observable : emit stream == reference emit stream
           legality   : independent replay of the admissibility rules
    C  adversarial fuzzing: hostile random snapshots, pathological
       abort rates, random wave partitions, random worker permutations
       (physical execution order inside a wave), artificial delays
       (modelled as extra attempt events).
    D  crash-stop runs (mirrors Lemma5.lean / FailSoundSubstrate):
       both machines halt at random points mid-journal; checks per run:
           forcedPrefix : proj(run) is a prefix of J
           refines      : result == Seq(P, consumed prefix)
           obs prefix   : emit stream is a prefix of the reference
                          (no fabricated observations)
           recovery     : Seq of the remainder from the crash state
                          lands on Seq(P,J) (factorization of
                          fail_substrate_independence)
    N  negative mode: intentionally broken substrates must be CAUGHT
       by the checker — wrong commit order, missing validation,
       scheduleCounter, an illegal wave partition, a wavefront without
       the entry-state barrier, two further schedule leaks (physical
       worker position, wave index), and two crash breakages
       (a fabricated post-halt emit, a torn commit).

Every run reports structural coverage and replay statistics, so an
"0 discrepancies" line can be read together with the evidence that the
generated cases actually exercised the machinery.  `--manifest FILE`
writes seeds, counts, coverage and results as JSON for reproduction.

The language, the instrumented semantics and both machines mirror
Lemma4.lean §0–§6 definition-for-definition (same names in comments);
phase D mirrors Lemma5.lean.
Q := Nat, oracle E q t := (q*7 + t) - 3, matching the emitted Lean.
"""

import argparse
import json
import platform
import random
import re
import subprocess
import sys
import tempfile
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEMMA4 = HERE / "Lemma4.lean"
if not LEMMA4.exists():                      # repo layout: witness/ next to lean/
    LEMMA4 = HERE.parent / "lean" / "Lemma4.lean"

CELLS = [f"c{i}" for i in range(5)]
VARS = [f"x{i}" for i in range(4)]
QTAGS = [0, 1, 2]          # Q := Nat
RHO0_DEFAULT = 0           # ρ₀ = fun _ => 0


def E_oracle(q: int, t: int) -> int:
    """E : Q → TxId → Int, mirrored verbatim in the emitted Lean."""
    return q * 7 + t - 3


# ----------------------------------------------------------------------
# Coverage and replay statistics
# ----------------------------------------------------------------------

class Stats:
    """Structural coverage plus replay statistics.

    Coverage answers "did the generated cases actually reach the
    interesting states?".  A green run with an empty bucket is not
    evidence, so `required` buckets make the run fail when never hit.
    """

    REQUIRED = [
        "instr:read", "instr:write", "instr:emit", "instr:ite", "instr:ext",
        "case:repeated_tx", "case:aborted", "case:read_own_write",
        "case:empty_readset", "case:multi_wave", "case:parallel_wave",
        "case:hostile_commit", "case:emitting",
    ]

    def __init__(self) -> None:
        self.cov: Counter[str] = Counter()
        self.attempts: list[int] = []       # attempts per committed transaction
        self.wave_sizes: Counter[int] = Counter()
        self.readset_sizes: list[int] = []
        self.events = 0
        self.commits = 0

    def hit(self, key: str, n: int = 1) -> None:
        self.cov[key] += n

    def census_body(self, b) -> None:
        stack = [b]
        while stack:
            n = stack.pop()
            tag = n[0]
            if tag == "done":
                continue
            self.hit(f"instr:{tag}")
            if tag in ("read", "write", "ext"):
                stack.append(n[3])
            elif tag == "emit":
                stack.append(n[2])
            elif tag == "ite":
                stack.extend([n[2], n[3]])

    def missing(self) -> list[str]:
        return [k for k in self.REQUIRED if not self.cov[k]]

    def report(self, indent: str = "  ") -> str:
        lines = ["Coverage:"]
        for k in sorted(self.cov):
            lines.append(f"{indent}{k:<26} {self.cov[k]}")
        if self.attempts:
            n = len(self.attempts)
            retried = sum(1 for a in self.attempts if a > 1)
            lines.append("Replay statistics:")
            lines.append(f"{indent}{'committed transactions':<26} {n}")
            lines.append(f"{indent}{'attempts per commit (avg)':<26} {sum(self.attempts)/n:.2f}")
            lines.append(f"{indent}{'attempts per commit (max)':<26} {max(self.attempts)}")
            lines.append(f"{indent}{'commits needing a retry':<26} "
                         f"{retried} ({100.0*retried/n:.1f}%)")
            lines.append(f"{indent}{'trace events replayed':<26} {self.events}")
        if self.readset_sizes:
            rs = self.readset_sizes
            lines.append(f"{indent}{'read-set size (avg / max)':<26} "
                         f"{sum(rs)/len(rs):.2f} / {max(rs)}")
        if self.wave_sizes:
            hist = " ".join(f"{k}:{v}" for k, v in sorted(self.wave_sizes.items()))
            lines.append(f"{indent}{'wave size histogram':<26} {hist}")
        return "\n".join(lines)

    def as_dict(self) -> dict:
        d = {"coverage": dict(sorted(self.cov.items())),
             "wave_sizes": {str(k): v for k, v in sorted(self.wave_sizes.items())},
             "trace_events": self.events, "commits": self.commits}
        if self.attempts:
            d["attempts_per_commit"] = {
                "avg": round(sum(self.attempts) / len(self.attempts), 4),
                "max": max(self.attempts),
                "retried": sum(1 for a in self.attempts if a > 1),
            }
        if self.readset_sizes:
            d["readset_size"] = {
                "avg": round(sum(self.readset_sizes) / len(self.readset_sizes), 4),
                "max": max(self.readset_sizes),
            }
        return d


# ----------------------------------------------------------------------
# §0  Language and reference sequential semantics (mirrors runBody/runSeq)
# ----------------------------------------------------------------------
# Expr  = ('const', n) | ('var', v) | ('add', a, b) | ('mul', a, b)
# Body  = ('done',) | ('read', c, x, k) | ('write', c, e, k)
#       | ('emit', e, k) | ('ite', e, b1, b2) | ('ext', q, x, k)

def eval_expr(rho: dict, e) -> int:
    tag = e[0]
    if tag == "const":
        return e[1]
    if tag == "var":
        return rho.get(e[1], RHO0_DEFAULT)
    if tag == "add":
        return eval_expr(rho, e[1]) + eval_expr(rho, e[2])
    if tag == "mul":
        return eval_expr(rho, e[1]) * eval_expr(rho, e[2])
    raise ValueError(tag)


def run_body(t: int, s: dict, rho: dict, o: list, b) -> tuple:
    """runBody E t : State → Env → Out → Body → State × Out (destructive-free)."""
    while True:
        tag = b[0]
        if tag == "done":
            return s, o
        if tag == "read":
            _, c, x, k = b
            rho = {**rho, x: s.get(c, 0)}
            b = k
        elif tag == "write":
            _, c, e, k = b
            s = {**s, c: eval_expr(rho, e)}
            b = k
        elif tag == "emit":
            _, e, k = b
            o = o + [eval_expr(rho, e)]
            b = k
        elif tag == "ite":
            _, e, b1, b2 = b
            b = b2 if eval_expr(rho, e) == 0 else b1
        elif tag == "ext":
            _, q, x, k = b
            rho = {**rho, x: E_oracle(q, t)}
            b = k
        else:
            raise ValueError(tag)


def run_seq(P: dict, s: dict, o: list, J: list) -> tuple:
    """runSeq: sequential fold of the journal, ρ₀ per transaction."""
    for t in J:
        s, o = run_body(t, s, {}, o, P[t])
    return s, o


# ----------------------------------------------------------------------
# §1  Instrumented semantics (mirrors runInstr / runTx / validates)
# ----------------------------------------------------------------------

def run_instr(t: int, sigma: dict, w: dict, rho: dict, o: list, rs: list, b, stats=None):
    while True:
        tag = b[0]
        if tag == "done":
            return w, o, rs
        if tag == "read":
            _, c, x, k = b
            if c in w:                      # read-your-own-writes
                if stats is not None:
                    stats.hit("case:read_own_write")
                rho = {**rho, x: w[c]}
            else:
                v = sigma.get(c, 0)
                rho = {**rho, x: v}
                rs = rs + [(c, v)]
            b = k
        elif tag == "write":
            _, c, e, k = b
            w = {**w, c: eval_expr(rho, e)}
            b = k
        elif tag == "emit":
            _, e, k = b
            o = o + [eval_expr(rho, e)]
            b = k
        elif tag == "ite":
            _, e, b1, b2 = b
            b = b2 if eval_expr(rho, e) == 0 else b1
        elif tag == "ext":
            _, q, x, k = b
            rho = {**rho, x: E_oracle(q, t)}
            b = k
        else:
            raise ValueError(tag)


def run_tx(t: int, sigma: dict, b, stats=None):
    """runTx: instrumented run from empty writes/env/out/readset."""
    w, o, rs = run_instr(t, sigma, {}, {}, [], [], b, stats)
    if stats is not None:
        stats.readset_sizes.append(len(rs))
        if not rs:
            stats.hit("case:empty_readset")
    return w, o, rs


def validates(S: dict, rs: list) -> bool:
    return all(S.get(c, 0) == v for c, v in rs)


def apply_w(S: dict, w: dict) -> dict:
    return {**S, **w}


# ----------------------------------------------------------------------
# §3  Substrate 1: optimistic trace machine (mirrors RunTrace / semProj)
# ----------------------------------------------------------------------

def perturb(s: dict, rng: random.Random, hostility: float) -> dict:
    """Adversarial snapshot: the current state with random cells corrupted."""
    sigma = dict(s)
    for c in CELLS:
        if rng.random() < hostility:
            sigma[c] = rng.randint(-9, 9)
    return sigma


def optimistic_run(P, s0, J, rng, hostility=0.3, max_attempts=25, delay_rate=0.0, stats=None):
    """Speculate with hostile snapshots; abort on validation failure;
    ordered commit.  Returns (events, state, out).  delay_rate injects
    extra attempt events (artificial delays are trace no-ops)."""
    s, o, events = dict(s0), [], []
    for t in J:
        attempts = 0
        while True:
            if rng.random() < delay_rate:
                events.append(("attempt", t, perturb(s, rng, 1.0)))
            attempts += 1
            # after too many hostile failures, take an honest snapshot
            sigma = dict(s) if attempts > max_attempts else perturb(s, rng, hostility)
            w, out, rs = run_tx(t, sigma, P[t], stats)
            if validates(s, rs):
                events.append(("commit", t, sigma))
                if stats is not None:
                    stats.attempts.append(attempts)
                    stats.commits += 1
                    if attempts > 1:
                        stats.hit("case:aborted")
                    if any(sigma.get(c, 0) != s.get(c, 0) for c in CELLS):
                        # committed from a snapshot that was never the real state
                        stats.hit("case:hostile_commit")
                s, o = apply_w(s, w), o + out
                break
            events.append(("attempt", t, sigma))
    if stats is not None:
        stats.events += len(events)
    return events, s, o


def sem_proj(events):
    return [t for kind, t, _ in events if kind == "commit"]


def abort_count(events):
    return sum(1 for kind, _, _ in events if kind == "attempt")


def replay_trace(P, s0, J, events):
    """Independent admissibility replay of RunTrace: returns final
    (state, out) or raises if any rule is violated."""
    s, o, j = dict(s0), [], list(J)
    for kind, t, sigma in events:
        if not j or j[0] != t:
            raise AssertionError(f"event on {t} but journal head is {j[:1]}")
        if kind == "attempt":
            continue                       # journal NOT consumed
        w, out, rs = run_tx(t, sigma, P[t])
        if not validates(s, rs):
            raise AssertionError(f"commit of {t} does not validate")
        s, o, j = apply_w(s, w), o + out, j[1:]
    if j:
        raise AssertionError(f"journal not fully consumed: {j}")
    return s, o


# ----------------------------------------------------------------------
# §5–§6  Substrate 2: wavefront machine (mirrors cellsOf/WaveOk/WaveRun)
# ----------------------------------------------------------------------

def cells_of(b) -> list:
    tag = b[0]
    if tag == "done":
        return []
    if tag in ("read", "write"):
        return [b[1]] + cells_of(b[3])
    if tag == "emit":
        return cells_of(b[2])
    if tag == "ite":
        return cells_of(b[2]) + cells_of(b[3])
    if tag == "ext":
        return cells_of(b[3])
    raise ValueError(tag)


def disj_cells(xs, ys) -> bool:
    return all(c not in ys for c in xs)


def wave_ok(P, ts) -> bool:
    for i, t in enumerate(ts):
        for u in ts[i + 1:]:
            if not disj_cells(cells_of(P[t]), cells_of(P[u])):
                return False
    return True


def random_partition(P, J, rng):
    """Random legal wave partition (greedy with random barriers)."""
    waves, cur, cur_cells = [], [], set()
    for t in J:
        fp = set(cells_of(P[t]))
        if cur and (fp & cur_cells or rng.random() < 0.35):
            waves.append(cur)
            cur, cur_cells = [], set()
        cur.append(t)
        cur_cells |= fp
    if cur:
        waves.append(cur)
    return waves


def wavefront_run(P, s0, waves, rng=None, stats=None, break_mode=None):
    """WaveRun: each wave executes against the FIXED wave-entry state;
    barrier merge in journal order; emits concatenated in journal
    order.  Physical execution order inside a wave is randomly
    permuted (worker permutation) — it must not matter.

    break_mode deliberately violates one rule at a time, for the
    negative suite:
        "no_barrier"    — transactions in a wave see each other's writes,
                          in physical (shuffled) order instead of the
                          fixed wave-entry state ("no_barrier_illegal"
                          does the same on a deliberately illegal wave)
        "emit_worker"   — emits concatenated in physical order
        "worker_leak"   — the physical position of a transaction inside
                          its wave leaks into the emitted values
        "partition_leak"— the wave index leaks into the emitted values
    """
    s, o = dict(s0), []
    for wi, ts in enumerate(waves):
        if break_mode not in ("illegal_partition", "no_barrier_illegal"):
            assert wave_ok(P, ts), "illegal wave passed to wavefront_run"
        if stats is not None:
            stats.wave_sizes[len(ts)] += 1
        S0 = dict(s)
        order = list(range(len(ts)))
        if rng is not None:
            rng.shuffle(order)             # random worker order
        results = {}
        live = dict(s)                     # only used by "no_barrier"
        for pos, i in enumerate(order):    # physical order: shuffled
            t = ts[i]
            if break_mode in ("no_barrier", "no_barrier_illegal"):
                w, out, rs = run_tx(t, live, P[t], stats)
                live = apply_w(live, w)
            else:
                w, out, rs = run_tx(t, S0, P[t], stats)
            if break_mode == "worker_leak":
                out = [v + pos for v in out]
            elif break_mode == "partition_leak":
                out = [v + wi for v in out]
            results[i] = (w, out, rs)
        merge = order if break_mode == "emit_worker" else range(len(ts))
        for i in merge:                    # barrier merge: journal order
            w, out, _rs = results[i]
            s = apply_w(s, w)
            o = o + out
    return s, o


def wave_proj(waves):
    return [t for ts in waves for t in ts]


# ----------------------------------------------------------------------
# Random generators (Phase A)
# ----------------------------------------------------------------------

def gen_expr(rng, depth=2):
    if depth == 0 or rng.random() < 0.4:
        return ("const", rng.randint(-5, 5)) if rng.random() < 0.5 \
            else ("var", rng.choice(VARS))
    op = rng.choice(["add", "mul"])
    return (op, gen_expr(rng, depth - 1), gen_expr(rng, depth - 1))


def gen_body(rng, depth=5):
    if depth == 0 or rng.random() < 0.18:
        return ("done",)
    tag = rng.choice(["read", "write", "emit", "ite", "ext", "write", "emit"])
    if tag == "read":
        return ("read", rng.choice(CELLS), rng.choice(VARS), gen_body(rng, depth - 1))
    if tag == "write":
        return ("write", rng.choice(CELLS), gen_expr(rng), gen_body(rng, depth - 1))
    if tag == "emit":
        return ("emit", gen_expr(rng), gen_body(rng, depth - 1))
    if tag == "ite":
        return ("ite", gen_expr(rng), gen_body(rng, depth - 2), gen_body(rng, depth - 2))
    return ("ext", rng.choice(QTAGS), rng.choice(VARS), gen_body(rng, depth - 1))


def gen_case(rng, ntx=4, jlen=6):
    P = {t: gen_body(rng) for t in range(ntx)}
    J = [rng.randrange(ntx) for _ in range(rng.randint(1, jlen))]
    s0 = {c: rng.randint(-5, 5) for c in CELLS}
    return P, J, s0


# ----------------------------------------------------------------------
# Phase A: differential check python run_seq == Lean #eval runSeq
# ----------------------------------------------------------------------

def expr_lean(e):
    tag = e[0]
    if tag == "const":
        return f"(.const ({e[1]} : Int))"
    if tag == "var":
        return f'(.var "{e[1]}")'
    return f"(.{tag} {expr_lean(e[1])} {expr_lean(e[2])})"


def body_lean(b):
    tag = b[0]
    if tag == "done":
        return ".done"
    if tag == "read":
        return f'(.read "{b[1]}" "{b[2]}" {body_lean(b[3])})'
    if tag == "write":
        return f'(.write "{b[1]}" {expr_lean(b[2])} {body_lean(b[3])})'
    if tag == "emit":
        return f"(.emit {expr_lean(b[1])} {body_lean(b[2])})"
    if tag == "ite":
        return f"(.ite {expr_lean(b[1])} {body_lean(b[2])} {body_lean(b[3])})"
    return f'(.ext {b[1]} "{b[2]}" {body_lean(b[3])})'


def phase_a(n, seed, verbose=True):
    rng = random.Random(seed)
    cases = [gen_case(rng) for _ in range(n)]
    chunks = ["def EQ : Nat → TxId → Int := fun q t => ((q * 7 + t : Nat) : Int) - 3\n"]
    for i, (P, J, s0) in enumerate(cases):
        arms = " ".join(f"| {t} => {body_lean(b)}" for t, b in P.items())
        state = "fun c => " + " else ".join(
            f'if c = "{c}" then ({s0[c]} : Int)' for c in CELLS) + " else 0"
        chunks.append(f"def P{i} : Program Nat := fun t => match t with {arms} | _ => .done")
        chunks.append(f"def S{i} : State := {state}")
        chunks.append(f"def J{i} : Journal := {list(J)}")
        chunks.append(f"def R{i} : Result := runSeq EQ P{i} S{i} ([] : Out) J{i}")
        probes = ", ".join(f'R{i}.1 "{c}"' for c in CELLS)
        chunks.append(f'#eval s!"CASE{i}|{{R{i}.2}}|{{[{probes}]}}"')
    src = LEMMA4.read_text() + "\n" + "\n".join(chunks) + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(src)
        tmp = f.name
    proc = subprocess.run(["lean", tmp], capture_output=True, text=True, timeout=1800)
    if proc.returncode != 0:
        print(proc.stderr[:4000])
        raise RuntimeError("Lean harness failed to compile")
    lean_results = {}
    for line in proc.stdout.splitlines():
        m = re.match(r'"CASE(\d+)\|\[(.*?)\]\|\[(.*?)\]"', line.strip())
        if m:
            i = int(m.group(1))
            out = [int(x) for x in m.group(2).split(",") if x.strip()]
            cells = [int(x) for x in m.group(3).split(",")]
            lean_results[i] = (out, cells)
    mismatches = 0
    for i, (P, J, s0) in enumerate(cases):
        s, o = run_seq(P, dict(s0), [], J)
        py = (o, [s.get(c, 0) for c in CELLS])
        if lean_results.get(i) != py:
            mismatches += 1
            print(f"  MISMATCH case {i}: python={py} lean={lean_results.get(i)}")
    if verbose:
        print(f"Phase A: {n} cases, python_seq vs Lean #eval runSeq — "
              f"{n - mismatches} agree, {mismatches} mismatches")
    Path(tmp).unlink(missing_ok=True)
    return mismatches


# ----------------------------------------------------------------------
# Phase B/C: parallel substrates vs reference, full checker
# ----------------------------------------------------------------------

def check_optimistic(P, J, s0, events, s, o) -> list:
    errs = []
    ref_s, ref_o = run_seq(P, dict(s0), [], J)
    if sem_proj(events) != list(J):
        errs.append("forced: semProj != J")
    if (s, o) != (ref_s, ref_o):
        # compare states on the full cell pool (dicts may differ in repr)
        if o != ref_o or any(s.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
            errs.append("sound: result != Seq(P,J)")
    if o != ref_o:
        errs.append("observable: emit != reference emit")
    try:
        rs, ro = replay_trace(P, s0, J, events)
        if ro != ref_o or any(rs.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
            errs.append("legality replay result != Seq(P,J)")
    except AssertionError as ex:
        errs.append(f"illegal trace: {ex}")
    return errs


def check_wavefront(P, J, s0, waves, ws, wo, ref_s, ref_o) -> list:
    """Independent admissibility replay of WaveOk/WaveRun plus the two
    substrate laws.  Mirrors check_optimistic for substrate 2."""
    errs = []
    if wave_proj(waves) != list(J):
        errs.append("wavefront forced: waveProj != J")
    for ts in waves:
        if not wave_ok(P, ts):
            errs.append(f"illegal wave: overlapping footprints in {ts}")
            break
    if wo != ref_o:
        errs.append("wavefront observable: emit != reference emit")
    if any(ws.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
        errs.append("wavefront sound: state != Seq(P,J)")
    return errs


def merge_conflicting_waves(P, waves):
    """Fuse the first pair of adjacent waves whose union is illegal.
    Returns None when the case offers no conflict to exploit."""
    for i in range(len(waves) - 1):
        fused = waves[i] + waves[i + 1]
        if not wave_ok(P, fused):
            return waves[:i] + [fused] + waves[i + 2:]
    return None


def phase_bc(n, seed, hostility, delay_rate, label, stats=None):
    rng = random.Random(seed)
    bad = aborts = waves_total = 0
    for _ in range(n):
        P, J, s0 = gen_case(rng)
        if stats is not None:
            for b in P.values():
                stats.census_body(b)
            if len(set(J)) < len(J):
                stats.hit("case:repeated_tx")
        # substrate 1: optimistic
        events, s, o = optimistic_run(P, s0, J, rng, hostility,
                                      delay_rate=delay_rate, stats=stats)
        errs = check_optimistic(P, J, s0, events, s, o)
        aborts += abort_count(events)
        # substrate 2: wavefront with random partition + worker permutation
        waves = random_partition(P, J, rng)
        waves_total += len(waves)
        ws, wo = wavefront_run(P, s0, waves, rng, stats)
        ref_s, ref_o = run_seq(P, dict(s0), [], J)
        errs += check_wavefront(P, J, s0, waves, ws, wo, ref_s, ref_o)
        # frame corollary: inside a legal wave the footprints are disjoint, so
        # dropping the wave-entry barrier must be invisible.  If this ever
        # differs, either WaveOk or the frame theorem is mis-transcribed.
        ns, no_ = wavefront_run(P, s0, waves, rng, break_mode="no_barrier")
        if no_ != ref_o or any(ns.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
            errs.append("frame: barrier-free wave run != Seq(P,J) on a legal partition")
        # cross-substrate: both machines, same (P,J) → same Result
        if wo != o or any(ws.get(c, 0) != s.get(c, 0) for c in CELLS):
            errs.append("cross-substrate: optimistic != wavefront")
        if stats is not None:
            if len(waves) > 1:
                stats.hit("case:multi_wave")
            if any(len(w) > 1 for w in waves):
                stats.hit("case:parallel_wave")
            if ref_o:
                stats.hit("case:emitting")
        if errs:
            bad += 1
            print(f"  DISCREPANCY {label}: {errs}\n    P={P}\n    J={J}\n    s0={s0}")
    print(f"Phase {label}: {n} cases, {bad} discrepancies "
          f"({aborts} aborts total, avg {waves_total/max(n,1):.1f} waves/case)")
    return bad


# ----------------------------------------------------------------------
# Phase D — crash-stop runs (mirrors Lemma5 / FailSoundSubstrate)
# ----------------------------------------------------------------------

def is_prefix(a: list, b: list) -> bool:
    return a == b[:len(a)]


def check_crash(P, J, s0, consumed, s, o, proj) -> list:
    """The four L5 checks for a crashed run that consumed `consumed`
    (a candidate prefix of J) and finished in (s, o) with semantic
    projection `proj`:
      forcedPrefix  — proj is a prefix of J;
      refines       — (s, o) == Seq(P, consumed prefix);
      fail_observable_prefix — o is a prefix of the reference emit
                      stream (no fabricated observations);
      recovery factorization — Seq of the remaining journal, resumed
                      from the crash state, lands exactly on Seq(P, J)
                      (clause (ii) of fail_substrate_independence).
    """
    errs = []
    ref_s, ref_o = run_seq(P, dict(s0), [], J)
    if not is_prefix(list(proj), list(J)):
        errs.append("forcedPrefix: projection is not a prefix of J")
        return errs  # the remaining checks presuppose a meaningful prefix
    pre_s, pre_o = run_seq(P, dict(s0), [], list(consumed))
    if o != pre_o or any(s.get(c, 0) != pre_s.get(c, 0) for c in CELLS):
        errs.append("crash refines: result != Seq(consumed prefix)")
    if not is_prefix(o, ref_o):
        errs.append("observable prefix: crashed emit stream fabricates output")
    rec_s, rec_o = run_seq(P, dict(s), list(o), list(J)[len(consumed):])
    if rec_o != ref_o or any(rec_s.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
        errs.append("recovery factorization: crash state + Seq(remainder) != Seq(P,J)")
    return errs


#: buckets phase D itself must reach, or the run proves nothing about L5
CRASH_REQUIRED = ("crash:none", "crash:midway", "crash:full", "crash:wave_barrier")


def phase_crash(n, seed, stats=None):
    """Random crash points on both substrates.

    Substrate 1 (optimistic): crash between transactions — the machine
    stops consuming the journal after a random number of commits
    (mirrors CrashRun: commits are atomic, `crash` is legal anywhere
    between them).  Substrate 2 (wavefront): crash at a wave barrier —
    a random prefix of the wave partition is executed.

    Checked per case: forcedPrefix, refines(prefix), observable prefix
    (no fabricated observations), recovery factorization.
    """
    rng = random.Random(seed)
    bad = 0
    for _ in range(n):
        P, J, s0 = gen_case(rng)
        if stats is not None:
            for b in P.values():
                stats.census_body(b)
        # substrate 1: optimistic crash-stop between transactions
        cut = rng.randint(0, len(J))
        events, s, o = optimistic_run(P, s0, J[:cut], rng, hostility=0.5, stats=stats)
        errs = check_crash(P, J, s0, J[:cut], s, o, sem_proj(events))
        if stats is not None:
            key = "crash:none" if cut == 0 else ("crash:full" if cut == len(J) else "crash:midway")
            stats.hit(key)
        # substrate 2: wavefront crash-stop at a wave barrier
        waves = random_partition(P, J, rng)
        k = rng.randint(0, len(waves))
        consumed = [t for wv in waves[:k] for t in wv]
        ws, wo = wavefront_run(P, s0, waves[:k], rng, stats)
        errs += check_crash(P, J, s0, consumed, ws, wo, wave_proj(waves[:k]))
        if stats is not None and 0 < k < len(waves):
            stats.hit("crash:wave_barrier")
        if errs:
            bad += 1
            print(f"  DISCREPANCY D: {errs}\n    P={P}\n    J={J}\n    cut={cut}\n    s0={s0}")
    missing = [] if stats is None else [k for k in CRASH_REQUIRED if not stats.cov[k]]
    if missing:
        print(f"Phase D: UNREACHED crash buckets {missing} — the run proves nothing about them")
        bad += 1
    print(f"Phase D (crash): {n} cases, {bad} discrepancies")
    return bad


# ----------------------------------------------------------------------
# Negative mode: broken substrates must be caught
# ----------------------------------------------------------------------

#: broken substrates that MUST be caught every single time — a rate below
#: 100% here is a hole in the checker, not a property of the model.
ALWAYS_CAUGHT = ("wrong_order", "schedule_counter", "wave_illegal_partition",
                 "crash_emit_after_halt", "crash_torn_commit")


def negative_mode(n, seed, cov=None):
    """Every entry is an intentionally broken substrate.  Some breakages
    are invisible in the observable for some cases — that is exactly the
    observable-coincidence layer of L3.5, so those only have to be caught
    at least once, while the structural ones must be caught always."""
    rng = random.Random(seed)
    stats = {k: [0, 0] for k in
             ("wrong_order", "no_validation", "schedule_counter",
              "wave_illegal_partition", "wave_no_barrier", "wave_emit_worker_order",
              "worker_id_leak", "partition_id_leak",
              "crash_emit_after_halt", "crash_torn_commit")}

    def record(name, caught):
        stats[name][0] += 1
        stats[name][1] += bool(caught)

    for _ in range(n):
        P, J, s0 = gen_case(rng)
        ref_s, ref_o = run_seq(P, dict(s0), [], J)
        waves = random_partition(P, J, rng)

        # 1. wrong commit order: swap two adjacent distinct journal entries
        idx = [i for i in range(len(J) - 1) if J[i] != J[i + 1]]
        if idx:
            i = rng.choice(idx)
            J_bad = list(J); J_bad[i], J_bad[i + 1] = J_bad[i + 1], J_bad[i]
            events, s, o = optimistic_run(P, s0, J_bad, rng, 0.0)
            errs = check_optimistic(P, J, s0, events, s, o)  # checked against TRUE J
            record("wrong_order", errs)

        # 2. missing validation: commit hostile snapshots unconditionally
        s, o, events = dict(s0), [], []
        for t in J:
            sigma = perturb(s, rng, 0.9)
            w, out, rs = run_tx(t, sigma, P[t])
            events.append(("commit", t, sigma))          # no validates() check!
            s, o = apply_w(s, w), o + out
        errs = check_optimistic(P, J, s0, events, s, o)
        record("no_validation", errs)

        # 3. scheduleCounter: leak abort count into the observable
        events, s, o = optimistic_run(P, s0, J, rng, 0.8)
        o_leaky = o + [abort_count(events)]
        errs = check_optimistic(P, J, s0, events, s, o_leaky)
        record("schedule_counter", errs)

        # 4. illegal wave partition: fuse two waves with overlapping
        #    footprints — WaveOk is violated, the checker must say so
        bad_waves = merge_conflicting_waves(P, waves)
        if bad_waves is not None:
            ws, wo = wavefront_run(P, s0, bad_waves, rng, break_mode="illegal_partition")
            errs = check_wavefront(P, J, s0, bad_waves, ws, wo, ref_s, ref_o)
            record("wave_illegal_partition", errs)

        # 5. no barrier, on a wave that should never have been formed: the
        #    transactions now race on shared cells in physical order.  Checked
        #    on the result alone, so the catch is not just "illegal partition".
        if bad_waves is not None:
            # a race need not show up under one physical order, so look a few
            # times before declaring the breakage invisible
            diverged = False
            for _ in range(4):
                ws, wo = wavefront_run(P, s0, bad_waves, rng,
                                       break_mode="no_barrier_illegal")
                diverged = diverged or wo != ref_o or any(
                    ws.get(c, 0) != ref_s.get(c, 0) for c in CELLS)
            record("wave_no_barrier", diverged)

        # 6. emits merged in physical order instead of journal order
        ws, wo = wavefront_run(P, s0, waves, rng, break_mode="emit_worker")
        record("wave_emit_worker_order",
               check_wavefront(P, J, s0, waves, ws, wo, ref_s, ref_o))

        # 7. worker-id leak: the physical position inside the wave reaches
        #    the emitted values
        ws, wo = wavefront_run(P, s0, waves, rng, break_mode="worker_leak")
        record("worker_id_leak", check_wavefront(P, J, s0, waves, ws, wo, ref_s, ref_o))

        # 8. partition-id leak: the wave index reaches the emitted values
        ws, wo = wavefront_run(P, s0, waves, rng, break_mode="partition_leak")
        record("partition_id_leak", check_wavefront(P, J, s0, waves, ws, wo, ref_s, ref_o))

        # 9. fabricated observation after a crash: the substrate halts
        #    mid-journal but emits one value it never computed.  The
        #    sneakiest fabrication is the CORRECT next reference value —
        #    the prefix law alone cannot see it, only `refines` against
        #    Seq(consumed prefix) can; past the end of the reference
        #    stream any extra value breaks the prefix law itself.
        cut = rng.randint(0, len(J))
        events, s, o = optimistic_run(P, s0, J[:cut], rng, 0.3)
        fabricated = ref_o[len(o)] if len(o) < len(ref_o) else 7
        record("crash_emit_after_halt",
               check_crash(P, J, s0, J[:cut], s, o + [fabricated], sem_proj(events)))

        # 10. torn commit: the crash lands "inside" a commit — part of the
        #     next transaction's write set is applied without the journal
        #     being consumed.  Atomicity of commit w.r.t. crash is exactly
        #     what CrashRun promises, so this must be caught.
        if cut < len(J):
            t_next = J[cut]
            w, _, _ = run_tx(t_next, dict(s), P[t_next])
            torn = next(((c, v) for c, v in w.items() if s.get(c, 0) != v), None)
            if torn is not None:
                s_bad = apply_w(s, {torn[0]: torn[1]})
                record("crash_torn_commit",
                       check_crash(P, J, s0, J[:cut], s_bad, o, sem_proj(events)))

    ok = True
    for name, (total, caught) in stats.items():
        rate = 100.0 * caught / max(total, 1)
        print(f"Negative [{name}]: {caught}/{total} caught ({rate:.1f}%)")
        if total == 0:
            print(f"  never exercised: {name}")
            ok = False
        elif name in ALWAYS_CAUGHT:
            if caught < total:
                ok = False
        elif caught == 0:
            # a breakage invisible in every single case would mean the
            # checker cannot see that dimension at all
            ok = False
    if cov is not None:
        cov["negative"] = {k: {"total": v[0], "caught": v[1]} for k, v in stats.items()}
    return 0 if ok else 1


# ----------------------------------------------------------------------

def lean_version() -> str | None:
    try:
        r = subprocess.run(["lean", "--version"], capture_output=True, text=True, timeout=60)
        return r.stdout.strip() or None
    except (OSError, subprocess.SubprocessError):
        return None


def main():
    ap = argparse.ArgumentParser(description="M₀ differential witness")
    ap.add_argument("phase", choices=["a", "b", "c", "d", "crash", "neg", "all"],
                    nargs="?", default="all")
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--n-a", type=int, default=40)
    ap.add_argument("--n-b", type=int, default=3000)
    ap.add_argument("--n-c", type=int, default=3000)
    ap.add_argument("--n-d", type=int, default=2000)
    ap.add_argument("--n-neg", type=int, default=400)
    ap.add_argument("--manifest", metavar="FILE",
                    help="write seeds, counts, coverage and results as JSON")
    ap.add_argument("--no-coverage-gate", action="store_true",
                    help="report coverage but do not fail on unreached buckets")
    args = ap.parse_args()

    started = time.time()
    stats = Stats()
    extra: dict = {}
    failures = 0
    results: dict = {}

    if args.phase in ("a", "all"):
        results["phase_a_mismatches"] = phase_a(args.n_a, args.seed)
        failures += results["phase_a_mismatches"]
    if args.phase in ("b", "all"):
        results["phase_b_discrepancies"] = phase_bc(
            args.n_b, args.seed + 1, hostility=0.3, delay_rate=0.1, label="B", stats=stats)
        failures += results["phase_b_discrepancies"]
    if args.phase in ("c", "all"):
        results["phase_c_discrepancies"] = phase_bc(
            args.n_c, args.seed + 2, hostility=0.85, delay_rate=0.4,
            label="C (adversarial)", stats=stats)
        failures += results["phase_c_discrepancies"]
    if args.phase in ("d", "crash", "all"):
        results["phase_d_discrepancies"] = phase_crash(args.n_d, args.seed + 4, stats=stats)
        failures += results["phase_d_discrepancies"]
    if args.phase in ("neg", "all"):
        results["negative_failures"] = negative_mode(args.n_neg, args.seed + 3, extra)
        failures += results["negative_failures"]

    if stats.cov:
        print(stats.report())
        # the global REQUIRED buckets are populated by phases B/C; a
        # standalone phase D run is gated by CRASH_REQUIRED instead
        missing = stats.missing() if args.phase in ("b", "c", "all") else []
        if missing:
            print("  UNREACHED (the run proves nothing about these): " + ", ".join(missing))
            if not args.no_coverage_gate:
                failures += 1

    if args.manifest:
        manifest = {
            "tool": "m0.py",
            "timestamp_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "duration_s": round(time.time() - started, 2),
            "python": platform.python_version(),
            "platform": platform.platform(),
            "lean": lean_version(),
            "seeds": {"base": args.seed, "phase_a": args.seed, "phase_b": args.seed + 1,
                      "phase_c": args.seed + 2, "negative": args.seed + 3,
                      "phase_d": args.seed + 4},
            "counts": {"a": args.n_a, "b": args.n_b, "c": args.n_c, "d": args.n_d,
                       "neg": args.n_neg},
            "phase": args.phase,
            "results": results,
            "passed": failures == 0,
            **stats.as_dict(),
            **extra,
        }
        Path(args.manifest).write_text(json.dumps(manifest, indent=2, sort_keys=False) + "\n")
        print(f"Manifest written to {args.manifest}")

    print("RESULT:", "ALL CHECKS PASSED" if failures == 0 else f"{failures} FAILURES")
    sys.exit(0 if failures == 0 else 1)


if __name__ == "__main__":
    main()
