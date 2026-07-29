# Schedule Independence of Observable Behaviour in Journal-Ordered Transactional Systems

**Extended abstract, M₀ v1.0**

## 1. Motivation

A recurring class of systems has a curious asymmetry in its contract. State is part of the
protocol: replicas must agree on it, an audit must reproduce it, a replay must land on it byte
for byte. The order in which work was physically executed is not part of the protocol at all:
it is an artifact of how many cores were available, which speculation aborted, how the work
was partitioned. Replicated state machines, deterministic simulation, exchange matching
engines and replayable services all live under this contract.

The engineering answer is well known and old: order the inputs, then execute them
deterministically. The interesting question is not whether ordering the inputs helps, but
where exactly the line runs. Which primitives may a language in such a system expose without
breaking replay, and which ones break it? Implementations answer this by convention. "Don't
call `clock()`, don't use a hash of a pointer, don't let anything see the retry count." Each
convention is defensible in isolation; together they are folklore, and folklore does not
compose. What is missing is a statement of the form: *these* observations are safe for *this*
reason, and here is a counterexample for everything on the other side of the line.

This work states that line and proves it for a minimal model.

## 2. Property X

Fix a system whose inputs are a program `P` and a journal `J`, an ordered list of transaction
identifiers. A run of the system produces a final state and an output stream. Call the output
stream the *Observable*; it is an explicit projection of the result, not the internal state.

> **Property X.** Any two admissible schedules for the same program and journal produce the
> same Observable.

Two remarks, both of which turned out to matter more than expected.

First, X must be stated over the Observable rather than over the internal state. Requiring
identical internal states rules out substrates that are perfectly acceptable in practice, for
example one that keeps a scratch cell alive after a retry. Requiring only "the same final
answer" is too weak: it says nothing about a system that emits along the way, which is exactly
what a replayable service does.

Second, "the same schedule" is not the right notion of sameness for schedules. Two runs may
differ in every operational detail and still be the same run semantically. The model therefore
needs a structural equivalence on schedules, not an extensional one, and that equivalence is
what carries the whole result.

## 3. The model M₀

M₀ is deliberately small: a body language over transactional cells, a journal, and an
execution discipline.

A **body** reads and writes cells, emits values, branches, and may invoke one further
primitive discussed below. Expressions read only locals. Every external observation is
factored through the cell interface, which is what makes the semantic universe closed. A
**program** maps transaction identifiers to bodies. A **journal** is a list of identifiers.

The reference semantics is the sequential fold:

```
Seq(P, J) = fold over J of "run the body of t against the current state"
```

with a fresh local environment per transaction. This is `runSeq` in the mechanization, and
Lemma 1 shows that the relational and executable versions agree and that the result is unique.

The parallel discipline has three rules:

1. a transaction executes **optimistically against a snapshot**, which need not be the current
   state and, in the adversarial reading, is chosen by an opponent;
2. at commit time its **read set is validated** against the real state;
3. commits happen **strictly in journal order**.

The primitive extension `ext q x` sets a local from an oracle `E : Q → TxId → Int`. Its type is
the boundary condition made syntactic: an oracle may look at a query and at the logical time,
which is the position in the journal, and at nothing else.

A **schedule** is reified as a trace of events: `attempt t σ` for a speculative attempt that
was discarded, `commit t σ` for a validated commit. The **semantic projection** `semProj` of a
trace is the list of committed identifiers in commit order. It carries the commit order, the
assignment of logical time, and the journal that was consumed. It does not carry abort counts,
snapshot choices, worker allocation, or timing. Two schedules are **semantically equivalent**,
written `S₁ ≈_J S₂`, when their semantic projections are equal.

## 4. Results

**L1, sequential determinism.** `Seq` is deterministic and its executable form is adequate:
`evalBody_det`, `lemma1_seq_deterministic`, `runSeq_sound`, `seq_unique_result`.

**L2, the discipline is sufficient.** Ordered commit together with snapshot validation refines
the reference: every legal parallel run equals `Seq(P, J)`. The proof factors through snapshot
adequacy, that a validated read set makes a snapshot run indistinguishable from a run against
the real state (`runInstr_snapshot_adequate`), and commit realization
(`commit_step`, `commit_evalBody`). Main theorem: `par_refines_seq`.

**L3A, the boundary from the allowed side.** For *every* query type `Q` and *every* oracle
`E : Q → TxId → Int`, the entire L2 development goes through: `lemma3A_extension_preservation`.
Since the oracle is a function of the journal position, this is the general statement that an
observation of the form `o = f(state, journal, logical time)` preserves X. Corollaries cover
the cases that motivated the question in the first place: events routed through the journal
are safe, and allocating a fresh cell by journal position is safe. Allocation as such is not
the problem.

**L3B, the boundary from the forbidden side.** Take the same disciplined machine, ordered
commit and validation intact, and let the oracle return the machine's attempt counter. Two
legal runs of the same program, journal and initial state, differing only in whether one
attempt was discarded, produce different Observables: `lemma3B_boundary_counterexample`. The
forbidden observation is not a particular feature such as allocation or timing. It is any
observation of the execution relation itself.

**Necessity.** Two of the three sides of the minimality triangle are proved rather than
asserted. Validation without ordered commit admits a non-deterministic outcome
(`order_necessary`); ordered commit without validation admits a lost update
(`validation_necessary`). The third side, granularity against achievable parallelism, is
supported experimentally only and is deliberately not claimed.

**L3.5, three levels that are usually fused.** Semantic equivalence implies observable
equivalence (`lemma3_5_equiv_implies_observable`), and all legal complete runs of one
`(P, J)` are pairwise `≈_J` (`same_journal_all_equiv`), so every difference between them is an
implementation artifact; `abort_count_artifact` exhibits two legal runs with different abort
counts. The converse fails: two runs with different semantic projections can happen to produce
equal Observables (`observable_coincidence_not_equiv`). The inclusions

```
semantic equivalence  ⊊  observable equivalence  ⊊  coincidence
```

are therefore strict, and equality of outputs without `≈_J` is a coincidence of
implementations rather than semantic identity. This is the layer that makes the informal
phrase "the schedule must not be observable" precise: an admissible observable must factor
through the semantic inputs, and everything not preserved by `semProj` belongs to one class,
of which the attempt counter of L3B is the canonical member.

**L4, substrate independence.** The final step promotes `≈_J` from a relation on traces of one
machine to an interface between machines. A `SoundSubstrate` is an arbitrary type of schedules
with a legality relation and a semantic projection, subject to two laws: the projection of a
legal run is exactly the consumed journal (`forced`), and every legal run refines the
sequential fold of its own projection (`refines`). Then:

- `substrate_independence`: for any two sound substrates and any two legal runs with equal
  semantic projections, the results, hence the Observables, coincide. The transfer invariant
  mentions neither machine's internals.
- `substrate_run_eq_seq`: every legal run on every sound substrate equals `Seq(P, J)`. M₀ is
  the equivalence class; substrates are its representatives.
- Two instances with disjoint vocabularies of artifacts are constructed. The optimistic trace
  machine has speculation, adversarial snapshots, validation and aborts. The wavefront machine
  is pessimistic and BSP-style: static conflict analysis on syntactic footprints, the journal
  cut into waves of pairwise non-conflicting transactions, every transaction of a wave running
  against the same wave-entry state, no snapshots, no validation, no aborts, write sets merged
  at the barrier. Its correctness rests on a non-interference (frame) theorem: disjoint static
  footprints imply that executing a whole wave against its entry state realizes the sequential
  fold (`wave_refines_seq`).
- Witnesses make the point concrete. Two wavefront runs of the same `(P, J)` with different
  partitions agree (`wave_partition_artifact`), and an optimistic run with an abort agrees with
  a single-wave parallel run (`cross_substrate_witness`).
- Completeness in the other direction: a substrate that implements M₀ executes as M₀ does
  (`implements_M0_execute_eq`).

In one sentence: for a closed, order-sensitive semantics with journal-ordered commit and
snapshot validation, the observable behaviour is a function of the journal and the semantic
state alone, and not of the execution schedule, for any substrate satisfying two interface
laws.

## 5. Mechanization and witness

Everything above is mechanized in **Lean 4.31.0**, five self-contained files with no
dependencies, not even Mathlib, so that `lean Lemma4.lean` reproduces the top result on a bare
toolchain. There are **no `sorry`s**. The axiom footprint is checked rather than claimed: CI
compares the axioms of nineteen headline theorems against a recorded list, so a proof that
starts depending on something new fails the build. `substrate_independence`,
`implements_M0_execute_eq` and the L1 theorems depend on no axioms at all; the rest use only
`propext` and `Quot.sound`.

A proof assistant checks the proofs, not the transcription of the model into them. The project
therefore ships an independent **differential witness**, `m0.py`, written against the paper
definitions rather than against the Lean text:

- **Phase A** generates random programs and compares a plain Python interpreter with Lean
  `#eval` of `runSeq`, which is the only check that the two transcriptions of the reference
  semantics agree.
- **Phases B and C** run both substrates against the reference under random and then hostile
  conditions (adversarial snapshots, abort storms, random partitions, random worker
  permutations), checking journal forcing, soundness, the emit stream, an independent replay
  of the admissibility rules, and cross-substrate agreement.
- **The negative suite** breaks the substrates on purpose. Three structural breakages, commits
  out of journal order, an attempt counter leaked into the output, and two conflicting
  transactions fused into one wave, must be caught in 100% of cases. Five further breakages,
  including missing validation, a race without the wave-entry barrier, and leaks of the worker
  position or the wave index into emitted values, are caught only part of the time, which is
  the empirical face of the coincidence layer of L3.5: damage that never reaches an emit is
  not observable in that case.
- **Coverage is gated.** Thirteen structural buckets, from instruction census to
  "a commit from a snapshot that was never the real state", must be non-empty or the run
  fails. A green run over cases that never enter the interesting states is not evidence.

A witness is a falsifier, not a second proof. Agreement raises confidence; a discrepancy is a
counterexample to the implementation or to the transcription, never to the theorem. Every run
writes a JSON manifest with seeds, versions, counts, coverage and per-breakage statistics, and
CI uploads it, so any published number can be traced to the run that produced it.

## 6. Limitations

Stated deliberately, because the value of the artifact depends on its boundary being visible.

- **No liveness.** M₀ says what a run may observe, never that a run terminates. The wavefront
  machine is total by construction, but progress under contention is not modelled.
- **No performance and no cost semantics.** The model has no notion of work, latency, or
  contention. Nothing here says that a substrate is fast, or even that it is faster than the
  sequential fold.
- **No scheduler optimality.** Wave partitioning is treated as an implementation artifact.
  Which partition to choose is outside the model.
- **No implementation engineering.** Both substrates are models. There is no storage engine,
  no recovery, no durability, no distribution.
- **Granularity is not claimed.** The third side of the minimality triangle, the trade-off
  between transaction granularity and achievable parallelism, has experimental support only.
- **Model scale.** Cells hold integers, bodies are finite, and the oracle is a pure function.
  The results are about the discipline, not about a production type system.

## 7. Future work

The natural next layer is **cost semantics**: attaching work to a run so that partitions and
schedules can be compared rather than merely declared equivalent. That brings in conflict
graphs, granularity as a formal parameter rather than an experimental observation, and a
performance model of the two substrates. Since it is a genuinely different pillar, it is
developed on a separate branch, leaving the safety story of v1.0 as a fixed reference point.

Beyond that: liveness and progress under contention; a substrate with genuine partial failure;
and mapping the boundary theorem onto an existing language's effect system to see how many of
its primitives fall on the allowed side.

## Artifact

`Topicspot/m0-semantics`, tag `v1.0`. Lean sources in `lean/`, witness in `witness/`, full
research log in `docs/STATE_OF_PROJECT_v5.1.md`. `python scripts/verify.py` reproduces
everything claimed here: build, absence of `sorry`, axiom footprint, witness. The manifest of
the reference run is attached to the release as `run-v1.0.json`.
