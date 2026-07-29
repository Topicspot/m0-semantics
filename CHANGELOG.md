# Changelog

## Unreleased

- **Lemma 5 (failure-tolerant substrate independence)** — `lean/Lemma5.lean`,
  the first post-v1.0 result, per the direction set by the related-work survey:
  the `forced` law of the L4 interface weakened from equality with the journal
  to a prefix of it (`FailSoundSubstrate`). Proved: prefix order of observables
  plus exact factorization between any two fail-sound substrates
  (`fail_substrate_independence`), crash-observable safety
  (`fail_observable_prefix`), conservativity over L4
  (`substrate_independence_of_fail`), the crash-stop optimistic machine as an
  instance, and a witness that the weakening is strict and its price exact
  (`crash_prefix_witness`). 0 `sorry`; axioms within propext/Quot.sound;
  `fail_substrate_independence_eq` and `runTrace_is_crashRun` axiom-free.
  Decision record: `docs/NEXT_STAGE.md`. No v1.0 statement is modified.

## v1.0 — 2026-07-29 — research artifact

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
- **Witness.** `m0.py` — differential check against Lean `#eval` in Phase A, two parallel
  substrates against the reference in Phases B and C, eight intentionally broken substrates in
  the negative suite, structural coverage with a gate that fails a run which never reached the
  interesting states, replay statistics, and a JSON manifest with seeds and versions.
- **Recovered history.** `docs/STATE_OF_PROJECT_v5.1.md` and `docs/RECOVERY.md` record the
  research log and the loss and recovery of the sources on 2026-07-29.
- **Repository.** Renamed from `new-language`; the earlier Weave language experiment is kept,
  frozen, under `weave/`.

Reference run at this tag: `witness/run-v1.0.json` — seed 2026, Phase A 40/40, Phase B and
Phase C 3 000 cases each with 0 discrepancies, 21 226 committed transactions, 2.02 attempts
per commit on average, every coverage bucket non-empty.

Not part of v1.0: cost semantics and granularity (next stage, `cost-semantics` branch),
liveness, an implementation, and the paper.
