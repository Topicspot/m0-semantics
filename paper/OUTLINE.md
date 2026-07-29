# Write-up plan

[`EXTENDED_ABSTRACT.md`](EXTENDED_ABSTRACT.md) is the current text and the intended entry
point for a reader: motivation, property X, the model, results L1 to L4, mechanization and
witness, limitations, future work.

The full paper, if it happens, expands the same skeleton rather than replacing it:

1. Problem. State is part of the protocol, the schedule is not. Replicated state machines,
   deterministic simulation, matching engines, replayable services.
2. Property X, and why "same result" is too weak while "same internal state" is too strong.
   The three levels of L3.5: semantic, observable, coincidence.
3. Model M₀ in full: syntax, instrumented semantics, snapshot adequacy, the commit rule.
4. L1 and L2 with proof sketches at the level of the snapshot-adequacy kernel.
5. L3A and L3B as a single boundary statement, with the necessity lemmas.
6. L3.5 with the strictness witnesses.
7. L4: the `SoundSubstrate` interface, the two instances, the frame theorem for waves.
8. Witness methodology: what a differential witness proves, what it cannot, coverage gating.
9. Related work: serializability theory, deterministic databases and replay systems,
   mechanized concurrency semantics. Not yet surveyed.
10. Limits and the cost-semantics programme.

Open before submission anywhere: a related-work survey (section 9) does not exist yet, and no
venue has been chosen.
