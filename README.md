# M₀ — deterministic state semantics

[![verify](https://github.com/Topicspot/m0-semantics/actions/workflows/verify.yml/badge.svg)](https://github.com/Topicspot/m0-semantics/actions/workflows/verify.yml)

M₀ is a small formal model of *state that stays part of the protocol while the schedule does
not*. It targets systems where a replayed run must produce byte-identical observable output —
replicated state machines, deterministic simulations, matching engines, database kernels.

The property under study, informally:

> if two schedules are semantically equivalent for the same journal, the observable output of
> the run is identical

Formally `schedule₁ ≈_J schedule₂ ⇒ Observable(run₁) = Observable(run₂)`, with the reference
`Seq(P, J) = fold(J)`.

The model: transactional cells, optimistic execution against a snapshot, snapshot validation
at commit, commit strictly in journal order.

## What v1.0 is

`v1.0` marks a finished research stage, not a finished research programme. It is a
reproducible artifact: everything claimed below is re-checked by CI on every commit.

**In v1.0**

| Layer | Content | State |
| --- | --- | --- |
| L1 | deterministic sequential fold | proved |
| L2 | ordered commit + validation ⇒ Parallel = Seq | proved |
| L3A / L3B | boundary of admissible extensions + `scheduleCounter` counterexample | proved |
| L3.5 | semantic ⊊ observable ⊊ coincidence | proved |
| L4 | substrate independence (`SoundSubstrate`, optimistic + wavefront instances) | proved |
| witness | `m0.py`: differential witness, 8 negative substrates, coverage gate, JSON manifest | green |

Mechanized in Lean 4.31.0 with `0 sorry`; the only axioms used are `propext` and `Quot.sound`,
and `substrate_independence` — the main theorem — uses none. The full axiom footprint is
compared against the documented one by `scripts/verify.py`, so a proof that silently starts
depending on something new fails CI.

**Not in v1.0, explicitly**

- Cost semantics and granularity: how much work a schedule does, conflict graphs, scheduler
  models, performance. This is the next research stage, developed on the `cost-semantics`
  branch, and nothing about it is claimed here.
- Liveness. M₀ is a safety story: it says what a run may observe, never that it finishes.
- An implementation. The two substrates are models, not a database or a runtime.
- A paper. `paper/` holds an outline; the extended abstract comes after v1.0.

Reference run at the tag (seed 2026): Phase A 40/40, Phase B and Phase C 3 000 cases each with
0 discrepancies, negative suite as in [witness/README.md](witness/README.md), all coverage
buckets non-empty. The manifest of that run is committed as
[`witness/run-v1.0.json`](witness/run-v1.0.json) and attached to the release; CI uploads the
manifest of every later run as an artifact.

The Lean sources were lost with the working chat on 29.07.2026 and recovered the same day;
every file was then re-checked from scratch. See [lean/README.md](lean/README.md) for the
per-file report and [docs/RECOVERY.md](docs/RECOVERY.md) for what happened.

## Layout

```
lakefile.toml, lean-toolchain
          Lake package pinned to Lean 4.31.0
scripts/  verify.py — the single command CI and humans both run
docs/     STATE_OF_PROJECT v5.1 (full research log, RU), recovery notes
lean/     the mechanization, Lemma1 … Lemma4 (Lean 4.31, no dependencies)
witness/  m0.py, the hostile differential witness
paper/    write-up outline
weave/    unrelated earlier project kept in this repo's history (see weave/README.md)
CHANGELOG.md
          what each release contains
```

## Quick start

Lean 4.31.0 (installed automatically by `elan` from `lean-toolchain`) and Python 3.10+.

```bash
lake build              # elaborate all five Lean files
python scripts/verify.py   # build + 0 sorry + axiom footprint + witness
```

`scripts/verify.py` is what CI runs; it prints `PASS` only if the build is clean, no source
contains `sorry`, every headline theorem has exactly the axiom footprint documented in
[lean/README.md](lean/README.md), and the witness reports `ALL CHECKS PASSED`. Add `--quick`
for a smaller witness run, `--skip-witness` for the Lean side only.

## Running the witness

Python 3.10+, standard library only.

```bash
python witness/m0.py b --n-b 2000      # parallel substrates vs reference
python witness/m0.py neg               # intentionally broken substrates must be caught
```

Expected: Phase B reports `0 discrepancies`; the negative suite catches the three structural
breakages (`wrong_order`, `schedule_counter`, `wave_illegal_partition`) in 100% of cases, and
the five observable-level ones — missing validation, a barrier-free race, emits in worker
order, a worker-id leak, a partition-id leak — only part of the time. That is not a bug but
the empirical face of observable coincidence from L3.5. Each run also reports structural
coverage and replay statistics, and fails if a required coverage bucket was never reached; see
[witness/README.md](witness/README.md).

`python witness/m0.py a` additionally requires `lean` on `PATH`; it builds a harness on top of
`lean/Lemma4.lean` and differentially compares the Python reference interpreter against
`#eval runSeq`.

## What the witness is, and is not

`m0.py` is a falsification / validation witness, not a second proof. Agreement over millions
of cases raises confidence. A discrepancy is a counterexample to the implementation or to the
transcription of the specification — never to the theorem.

## License

Dual licensed under Apache-2.0 and MIT.
