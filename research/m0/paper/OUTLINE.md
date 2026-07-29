# Write-up outline (draft)

Not started. Placeholder so the intended shape is not lost again.

1. Problem — state is part of the protocol, the schedule must not be. Replicated state
   machines, deterministic simulation, matching engines, database kernels.
2. Property X and why the naive formulation ("same result") is too weak and "same internal
   state" too strong. The three levels of L3.5: semantic, observable, coincidence.
3. Model M₀ — transactional cells, optimistic execution against a snapshot, validation,
   ordered commit. Reference `Seq(P, J) = fold(J)`.
4. Results L1–L4, with substrate independence as the main theorem.
5. Witness methodology — what a differential witness proves and what it cannot.
6. Limits — no cost semantics, no granularity theorem, no liveness. Next layer.
