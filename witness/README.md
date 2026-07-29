# Witness

`m0.py` — external hostile executor and differential witness for the M₀ mechanization.
Python 3.10+, standard library only, no arguments required.

```bash
python m0.py b --n-b 3000      # parallel substrates vs reference
python m0.py c --n-c 3000      # adversarial fuzzing (85% hostile snapshots)
python m0.py neg               # broken substrates must be caught
python m0.py all               # everything, including Phase A
```

Phases:

- **A** — random AST programs, pure sequential interpreter, differential check
  `python_seq == Lean #eval runSeq`. Requires `lean` on `PATH`; the harness is built on top of
  `../lean/Lemma4.lean`.
- **B** — parallel trace generator (attempt / snapshot / abort / commit) plus a wavefront
  generator with random partitions and random worker permutations. Per trace it checks
  `forced` (proj == J), `sound` (result == Seq(P,J)), `observable` (emit stream equals the
  reference), independent replay of the admissibility rules, and cross-substrate agreement.
- **C** — adversarial fuzzing: hostile snapshots, abort storms, artificial delays.
- **neg** — intentionally broken substrates. `wrong_order` and `schedule_counter` must be
  caught in 100% of cases; `no_validation` is caught roughly half the time, which is the
  expected empirical face of observable coincidence (a corrupted cell that the body never
  reads yields the same observable result).

Recorded full run, two seeds: Phase A 100/100 agree, Phase B+C 106 000 cases with 0
discrepancies and ~580 000 aborts, negative mode wrong order 1851/1851, scheduleCounter
2400/2400, missing validation ~49.5%.

Re-run after the recovery (Lean 4.31.0, seed 2026): Phase A 40/40, Phase B 3 000 cases and
Phase C 3 000 cases with 0 discrepancies, `wrong_order` 317/317, `schedule_counter` 400/400,
`no_validation` 198/400 (49.5%).

Open review items, not yet done: coverage counters, a seed manifest in JSON, negative tests
for wavefront rejection, and two or three more schedule-dependent leaks (worker id,
partition) alongside `scheduleCounter`.
