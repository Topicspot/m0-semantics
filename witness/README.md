# Witness

`m0.py` — external hostile executor and differential witness for the M₀ mechanization.
Python 3.10+, standard library only, no arguments required.

```bash
python m0.py b --n-b 3000      # parallel substrates vs reference
python m0.py c --n-c 3000      # adversarial fuzzing (85% hostile snapshots)
python m0.py neg               # broken substrates must be caught
python m0.py all               # everything, including Phase A
python m0.py all --manifest run.json   # reproducible record of the run
```

Phases:

- **A** — random AST programs, pure sequential interpreter, differential check
  `python_seq == Lean #eval runSeq`. Requires `lean` on `PATH`; the harness is built on top of
  `../lean/Lemma4.lean`.
- **B** — parallel trace generator (attempt / snapshot / abort / commit) plus a wavefront
  generator with random partitions and random worker permutations. Per trace it checks
  `forced` (proj == J), `sound` (result == Seq(P,J)), `observable` (emit stream equals the
  reference), independent replay of the admissibility rules, cross-substrate agreement, and
  the frame corollary — inside a legal wave the entry-state barrier is redundant, because the
  footprints are disjoint.
- **C** — adversarial fuzzing: hostile snapshots, abort storms, artificial delays.
- **neg** — intentionally broken substrates, listed below.

## Negative suite

| Breakage | Must be caught | Typical rate |
| --- | --- | --- |
| `wrong_order` — commit order deviates from the journal | always | 100% |
| `schedule_counter` — abort count leaks into the observable | always | 100% |
| `wave_illegal_partition` — two conflicting transactions fused into one wave | always | 100% |
| `no_validation` — hostile snapshots committed without validation | at least once | ~48% |
| `wave_no_barrier` — racing on shared cells with no wave-entry state | at least once | ~4% |
| `wave_emit_worker_order` — emits merged in physical, not journal, order | at least once | ~9% |
| `worker_id_leak` — physical position inside the wave reaches the emitted values | at least once | ~29% |
| `partition_id_leak` — wave index reaches the emitted values | at least once | ~53% |

The three structural breakages must be caught in 100% of cases; anything less is a hole in the
checker. The rest are only required to be caught at least once, and the fact that they are
*not* always caught is the empirical face of observable coincidence from L3.5: a broken
substrate whose damage never reaches an emit is, for that case, observationally equivalent to
the correct one. The rates are stable across seeds; a rate collapsing to 0 fails the run.

## Coverage and statistics

Every B/C run reports how much of the machinery the random cases actually reached: instruction
census, cases with repeated transactions, aborted transactions, read-your-own-write,
empty read-sets, multi-wave partitions, waves with real parallelism, commits from a snapshot
that was never the real state. Thirteen buckets are declared *required*: if one of them is
never hit the run fails, because a green run over cases that never enter the interesting
states is not evidence. Use `--no-coverage-gate` to report without enforcing.

Replay statistics: committed transactions, attempts per commit (average and maximum), share of
commits that needed a retry, replayed trace events, read-set sizes, wave size histogram.

## Manifest

`--manifest FILE` writes a JSON record of the run: timestamp, duration, Python and Lean
versions, platform, per-phase seeds, case counts, per-phase results, the coverage and replay
statistics, and the negative table with `total`/`caught` per breakage. CI runs
`scripts/verify.py`, which always writes `witness-manifest.json` and uploads it as a build
artifact, so any published number can be traced to the run that produced it.

## Reference run

Lean 4.31.0, seed 2026, `python m0.py all`: Phase A 40/40, Phase B and Phase C 3 000 cases
each with 0 discrepancies (~35 000 aborts), negative suite as in the table, 21 226 committed
transactions, 2.02 attempts per commit on average (max 26), all coverage buckets non-empty.
Earlier long runs on two seeds: 106 000 cases, 0 discrepancies.

## What the witness is, and is not

`m0.py` is a falsification / validation witness, not a second proof. Agreement over many cases
raises confidence. A discrepancy is a counterexample to the implementation or to the
transcription of the specification — never to the theorem.
