# Changelog

## v1.1 (2026-07-29): failure refinement

The safety story extended to partial failures. v1.0 stays the frozen reference point; nothing
in it changed meaning.

- **Lemma 5 (failure-tolerant substrate independence)**, `lean/Lemma5.lean`: direction set
  by the related-work survey: the `forced` law of the L4 interface weakened from equality
  with the journal to a *prefix* of it (`FailSoundSubstrate`). Proved: prefix monotonicity of
  the reference fold (`seq_out_prefix`); prefix order of observables plus exact factorization
  of the longer run through the shorter run's result between any two fail-sound substrates
  (`fail_substrate_independence`: the factorization clause is a strong form of recovery
  independence); crash-observable safety (`fail_observable_prefix`: a crash truncates, never
  fabricates); conservativity over L4 (`SoundSubstrate.toFail`,
  `substrate_independence_of_fail`); the crash-stop optimistic machine as an instance
  (`CrashRun`, strictly extending substrate 1); and a witness that the weakening is strict and
  its price exact (`crash_prefix_witness`). 0 `sorry`; axioms within propext/Quot.sound;
  `fail_substrate_independence_eq` and `runTrace_is_crashRun` axiom-free. Eleven new headline
  theorems in the axiom-footprint gate (thirty total). Decision record: `docs/NEXT_STAGE.md`.
- **Witness phase D (crash)**: L5 exercised experimentally. Both machines halt at random
  points (between transactions / at a wave barrier); every crashed run is checked against the
  four L5 laws (prefix forcing, refinement of the consumed prefix, observable prefix, recovery
  factorization), with a phase-local coverage gate. The negative suite gains two breakages
  that must be caught in 100% of cases: `crash_emit_after_halt` (in the hard variant the
  fabricated value equals the correct next reference value, invisible to the prefix law alone)
  and `crash_torn_commit` (a crash inside a commit).
- **Extended abstract updated** to v1.1: L5 in the results ladder, an explicit Failure Model
  section, mechanization counts, phase D, limitations and future work refreshed.

Reference run at this tag, `witness/run-v1.1.json`: seed 2026, Phase A 40/40, Phases B and C
3 000 cases each and Phase D 2 000 cases with 0 discrepancies, negative suite with both crash
breakages at 100%, all coverage buckets non-empty.

## v1.0 (2026-07-29): research artifact

First stable point of the M₀ line. The tag is immutable: later fixes ship as `v1.0.1`, `v1.1`
and so on, and this release stays as the reference point.

- **Mechanization L1–L4** in Lean 4.31.0, five standalone files, no dependencies:
  deterministic sequential fold; ordered commit with validation refining `Seq(P, J)`; the
  boundary of admissible extensions with the `scheduleCounter` counterexample and the
  necessity lemmas for order and validation; the strictness of semantic ⊊ observable ⊊
  coincidence; substrate independence over the `SoundSubstrate` interface with an optimistic
  and a wavefront instance.
- **`0 sorry`, verified rather than asserted.** `scripts/verify.py` compares the axiom
  footprint of nineteen headline theorems against the documented one, so `sorryAx` or any new
  axiom fails the build. `substrate_independence`, `implements_M0_execute_eq` and the L1
  theorems depend on no axioms at all.
- **CI.** Every push runs `lake build`, the source and axiom checks, and the witness, and
  uploads the run manifest as an artifact.
- **Witness.** `m0.py`: differential check against Lean `#eval` in Phase A, two parallel
  substrates against the reference in Phases B and C, eight intentionally broken substrates in
  the negative suite, structural coverage with a gate that fails a run which never reached the
  interesting states, replay statistics, and a JSON manifest with seeds and versions.
- **Recovered history.** `docs/STATE_OF_PROJECT_v5.1.md` and `docs/RECOVERY.md` record the
  research log and the loss and recovery of the sources on 2026-07-29.
- **Repository.** Renamed from `new-language`; the earlier Weave language experiment is kept,
  frozen, under `weave/`.

Reference run at this tag, `witness/run-v1.0.json`: seed 2026, Phase A 40/40, Phase B and
Phase C 3 000 cases each with 0 discrepancies, 21 226 committed transactions, 2.02 attempts
per commit on average, every coverage bucket non-empty.

Not part of v1.0: cost semantics and granularity (next stage, `cost-semantics` branch),
liveness, an implementation, and the paper.
