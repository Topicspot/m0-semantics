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
    N  negative mode: intentionally broken substrates
       (wrong commit order / missing validation / scheduleCounter
       observable injection) must be CAUGHT by the checker.

The language, the instrumented semantics and both machines mirror
Lemma4.lean §0–§6 definition-for-definition (same names in comments).
Q := Nat, oracle E q t := (q*7 + t) - 3, matching the emitted Lean.
"""

import argparse
import random
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEMMA4 = HERE / "Lemma4.lean"

CELLS = [f"c{i}" for i in range(5)]
VARS = [f"x{i}" for i in range(4)]
QTAGS = [0, 1, 2]          # Q := Nat
RHO0_DEFAULT = 0           # ρ₀ = fun _ => 0


def E_oracle(q: int, t: int) -> int:
    """E : Q → TxId → Int, mirrored verbatim in the emitted Lean."""
    return q * 7 + t - 3


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

def run_instr(t: int, sigma: dict, w: dict, rho: dict, o: list, rs: list, b):
    while True:
        tag = b[0]
        if tag == "done":
            return w, o, rs
        if tag == "read":
            _, c, x, k = b
            if c in w:                      # read-your-own-writes
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


def run_tx(t: int, sigma: dict, b):
    """runTx: instrumented run from empty writes/env/out/readset."""
    return run_instr(t, sigma, {}, {}, [], [], b)


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


def optimistic_run(P, s0, J, rng, hostility=0.3, max_attempts=25, delay_rate=0.0):
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
            w, out, rs = run_tx(t, sigma, P[t])
            if validates(s, rs):
                events.append(("commit", t, sigma))
                s, o = apply_w(s, w), o + out
                break
            events.append(("attempt", t, sigma))
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


def wavefront_run(P, s0, waves, rng=None):
    """WaveRun: each wave executes against the FIXED wave-entry state;
    barrier merge in journal order; emits concatenated in journal
    order.  Physical execution order inside a wave is randomly
    permuted (worker permutation) — it must not matter."""
    s, o = dict(s0), []
    for ts in waves:
        assert wave_ok(P, ts)
        S0 = dict(s)
        order = list(range(len(ts)))
        if rng is not None:
            rng.shuffle(order)             # random worker order
        results = {}
        for i in order:                    # physical order: shuffled
            t = ts[i]
            results[i] = run_tx(t, S0, P[t])
        for i in range(len(ts)):           # barrier merge: journal order
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


def phase_bc(n, seed, hostility, delay_rate, label):
    rng = random.Random(seed)
    bad = aborts = waves_total = 0
    for _ in range(n):
        P, J, s0 = gen_case(rng)
        # substrate 1: optimistic
        events, s, o = optimistic_run(P, s0, J, rng, hostility, delay_rate=delay_rate)
        errs = check_optimistic(P, J, s0, events, s, o)
        aborts += abort_count(events)
        # substrate 2: wavefront with random partition + worker permutation
        waves = random_partition(P, J, rng)
        waves_total += len(waves)
        ws, wo = wavefront_run(P, s0, waves, rng)
        ref_s, ref_o = run_seq(P, dict(s0), [], J)
        if wave_proj(waves) != list(J):
            errs.append("wavefront forced: waveProj != J")
        if wo != ref_o or any(ws.get(c, 0) != ref_s.get(c, 0) for c in CELLS):
            errs.append("wavefront sound: result != Seq(P,J)")
        # cross-substrate: both machines, same (P,J) → same Result
        if wo != o or any(ws.get(c, 0) != s.get(c, 0) for c in CELLS):
            errs.append("cross-substrate: optimistic != wavefront")
        if errs:
            bad += 1
            print(f"  DISCREPANCY {label}: {errs}\n    P={P}\n    J={J}\n    s0={s0}")
    print(f"Phase {label}: {n} cases, {bad} discrepancies "
          f"({aborts} aborts total, avg {waves_total/max(n,1):.1f} waves/case)")
    return bad


# ----------------------------------------------------------------------
# Negative mode: broken substrates must be caught
# ----------------------------------------------------------------------

def negative_mode(n, seed):
    rng = random.Random(seed)
    stats = {"wrong_order": [0, 0], "no_validation": [0, 0], "schedule_counter": [0, 0]}

    for _ in range(n):
        P, J, s0 = gen_case(rng)

        # 1. wrong commit order: swap two adjacent distinct journal entries
        idx = [i for i in range(len(J) - 1) if J[i] != J[i + 1]]
        if idx:
            i = rng.choice(idx)
            J_bad = list(J); J_bad[i], J_bad[i + 1] = J_bad[i + 1], J_bad[i]
            events, s, o = optimistic_run(P, s0, J_bad, rng, 0.0)
            errs = check_optimistic(P, J, s0, events, s, o)  # checked against TRUE J
            stats["wrong_order"][0] += 1
            stats["wrong_order"][1] += bool(errs)

        # 2. missing validation: commit hostile snapshots unconditionally
        s, o, events = dict(s0), [], []
        for t in J:
            sigma = perturb(s, rng, 0.9)
            w, out, rs = run_tx(t, sigma, P[t])
            events.append(("commit", t, sigma))          # no validates() check!
            s, o = apply_w(s, w), o + out
        errs = check_optimistic(P, J, s0, events, s, o)
        stats["no_validation"][0] += 1
        stats["no_validation"][1] += bool(errs)

        # 3. scheduleCounter: leak abort count into the observable
        events, s, o = optimistic_run(P, s0, J, rng, 0.8)
        o_leaky = o + [abort_count(events)]
        errs = check_optimistic(P, J, s0, events, s, o_leaky)
        stats["schedule_counter"][0] += 1
        stats["schedule_counter"][1] += bool(errs)

    ok = True
    for name, (total, caught) in stats.items():
        rate = 100.0 * caught / max(total, 1)
        print(f"Negative [{name}]: {caught}/{total} caught ({rate:.1f}%)")
        # wrong_order / schedule_counter must essentially always be caught;
        # no_validation may coincidentally agree when hostile reads are unused
        if name in ("wrong_order", "schedule_counter") and caught < total:
            ok = ok and (total - caught) == 0
        if name == "no_validation" and caught == 0:
            ok = False
    return 0 if ok else 1


# ----------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="M₀ differential witness")
    ap.add_argument("phase", choices=["a", "b", "c", "neg", "all"], nargs="?", default="all")
    ap.add_argument("--seed", type=int, default=2026)
    ap.add_argument("--n-a", type=int, default=40)
    ap.add_argument("--n-b", type=int, default=3000)
    ap.add_argument("--n-c", type=int, default=3000)
    ap.add_argument("--n-neg", type=int, default=400)
    args = ap.parse_args()

    failures = 0
    if args.phase in ("a", "all"):
        failures += phase_a(args.n_a, args.seed)
    if args.phase in ("b", "all"):
        failures += phase_bc(args.n_b, args.seed + 1, hostility=0.3, delay_rate=0.1, label="B")
    if args.phase in ("c", "all"):
        failures += phase_bc(args.n_c, args.seed + 2, hostility=0.85, delay_rate=0.4, label="C (adversarial)")
    if args.phase in ("neg", "all"):
        failures += negative_mode(args.n_neg, args.seed + 3)

    print("RESULT:", "ALL CHECKS PASSED" if failures == 0 else f"{failures} FAILURES")
    sys.exit(0 if failures == 0 else 1)


if __name__ == "__main__":
    main()
