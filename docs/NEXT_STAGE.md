# Next stage after v1.0: strengthening L4, not cost semantics

Decision record, 2026-07-29. v1.0 is frozen; nothing below changes a v1.0 claim.

## The choice

The plan on file offered two directions: the original cost-semantics branch
(granularity, conflict graphs, scheduler models) and, after the literature
survey, pushing the substrate interface further. The survey itself settled it
(`paper/RELATED_WORK.md`, "Effect on the next stage"): granularity has an
established neighbour in DPJ-style effect systems, while the interface theorem
L4 is the contribution the survey found most defensible. Strengthening the most
defensible claim dominates adding a second-most-defensible one.

Candidates considered for the strengthening, in the order of the project brief:

1. **Substrates with partial failure** — weaken `forced` from
   `proj sc = J` to `proj sc <+: J` (a prefix). **Chosen first**: it is the
   exact weakening the survey named, it has a crisp exact answer (see below),
   and every deterministic-database neighbour (Calvin, Aria, VerIso) treats
   recovery/failure as a separate systems concern rather than part of the
   correctness interface.
2. **Coarser journal projection** (e.g. projection up to a quotient, batches
   without internal order) — deferred: it changes the *type* of the transfer
   invariant and needs a worked-out candidate quotient to avoid a vacuous
   theorem. Natural second step; the prefix order introduced here is its
   simplest non-trivial special case.
3. **Weakened forced-law in general** — subsumed by 1 and 2; "arbitrary
   relaxation" is not a theorem statement.
4. **Incomplete observability** (observing a sub-stream of `Out`) — deferred:
   it modifies `Observable`, which sits inside frozen v1.0 statements; doing it
   later as a projection *on top of* `Out` keeps v1.0 untouched.

## What Lemma5.lean establishes (mechanized, 0 sorry)

Interface `FailSoundSubstrate` = L4's `SoundSubstrate` with
`forcedPrefix : proj sc <+: J`; `refines` unchanged. Crashing is legal,
deviating is not. Results:

- `seq_out_prefix` — sequential prefix monotonicity: a prefix of the journal
  emits a prefix of the reference observable. A property of `Seq` alone.
- `fail_substrate_independence` — for any two fail-sound substrates on the same
  journal, projection-prefix order implies (i) prefix order of observables and
  (ii) exact factorization of the longer run through the shorter run's result.
  Under partial failure, runs of different machines never diverge — they only
  stop.
- `fail_observable_prefix` — crash-observable safety: any legal run's
  observable is a prefix of `Seq(P, J)`'s. A crash can truncate output, never
  fabricate it.
- `fail_substrate_independence_eq`, `substrate_independence_of_fail`,
  `SoundSubstrate.toFail` — conservativity: L4 is literally the total fragment
  of the new interface; the v1.0 theorem is re-derived, not re-proved.
- `CrashRun` + `crashOptimisticSubstrate` — instance: the L3.5 optimistic trace
  machine with one new legal event (halting mid-journal). `runTrace_is_crashRun`
  embeds every total run, so the machine strictly extends substrate 1.
- `crash_prefix_witness` — strictness and exactness in one witness: a crashed
  run whose projection violates the L4 `forced` law (so the weakening is
  strict), whose observable differs from the total run's (so observable
  *equality* is genuinely lost), and is a prefix of it (so the prefix law is
  exactly what survives).

The trade is exact: weakening `forced` from equality to prefix weakens the
conclusion from equality of observables to prefix order of observables, and
nothing else. That exactness is the claim.

## What is NOT claimed

- Nothing about **recovery**: a crashed run is never resumed here. Recovery is
  liveness/implementation, outside X, exactly as fairness was outside L2.
- Nothing about **where** a substrate may crash: any prefix is admissible. A
  substrate that can only crash at wave barriers is a refinement, not proved.
- No claim of novelty for "crashes truncate output" as folklore; the candidate
  contribution is the *interface-level* form: two laws, quantification over
  substrates, mechanized, with the exact-price statement.

## Positioning against the literature (hypotheses, to verify while writing)

- VerIso (VLDB 2025) proves per-protocol refinement; a failure-tolerant
  *interface* theorem is not a per-protocol statement. Still must be read in
  full before any claim (unchanged from v1.0's obligation).
- The security line (observational determinism) does not, to our knowledge,
  treat crash-truncated traces as a first-class case with a prefix-ordered
  conclusion; prefix-closure of hyperproperties (Clarkson–Schneider 2-safety
  machinery) is the right vocabulary to check against.

## Follow-ups

1. Extend `witness/m0.py` with a crash mode: run the optimistic machine on a
   random prefix, check the emitted stream is a prefix of the reference and the
   state equals `Seq` of the consumed prefix (negative: a substrate that emits
   after halting must be caught).
2. Candidate next weakening: coarser projection (quotient journals), using the
   prefix order here as the template for "weaker law ⇒ exactly which weaker
   conclusion".
3. Wavefront machine with crash at wave barriers — a second, structurally
   different fail-sound instance; would make the interface's generality
   concrete the same way substrate 2 did for L4.
