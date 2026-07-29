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
9. Related work: see [`RELATED_WORK.md`](RELATED_WORK.md) for the matrix. Six groups:
   serializability theory, deterministic transaction processing, correctness conditions and
   their mechanization, refinement and verified systems, deterministic execution and replay,
   deterministic parallelism in languages.
10. Limits and the cost-semantics programme.

Open before submission anywhere: read VerIso (VLDB 2025) and Zdancewic and Myers (CSFW 2003)
in full and position the contribution against them precisely; no venue has been chosen.
