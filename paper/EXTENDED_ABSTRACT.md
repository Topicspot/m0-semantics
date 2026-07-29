# Schedule Independence of Observable Behaviour in Journal-Ordered Transactional Systems

**Extended abstract, M₀ v1.1**

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

This work states that line and proves it for a minimal model. The folklore rules are not
independent conventions: they are one class (this is a theorem below, L3A/L3B, not a slogan).
Every safe observation factors through the journal and the semantic state; every unsafe one
observes the execution relation itself, and one mechanized counterexample covers them all. That single criterion, not any particular rule,
is what the model is built to state and prove.

Concretely, the reader will find five results, each a strict step past the previous one, all
machine-checked with no `sorry` and cross-validated by an independent differential witness:
a deterministic sequential reference (L1); a proof that ordered commit plus snapshot
validation makes any parallel schedule agree with that reference (L2); the boundary criterion
with both a preservation schema and a counterexample (L3); the strict separation of semantic
equivalence, observable equivalence and accidental coincidence (L3.5); an interface theorem
making the whole story independent of the executing machine (L4); and its extension to
machines that may crash mid-run (L5).

## 2. Property X

Fix a system whose inputs are a program `P` and a journal `J`, an ordered list of transaction
identifiers. A run of the system produces a final state and an output stream. Call the output
stream the *Observable*; it is an explicit projection of the result, not the internal state.

> **Property X.** Any two admissible schedules for the same program and journal produce the
> same Observable.

Two remarks, both of which turned out to matter more than expected.

First — a design argument rather than a theorem — X must be stated over the Observable
rather than over the internal state. Requiring
identical internal states rules out substrates that are perfectly acceptable in practice, for
example one that keeps a scratch cell alive after a retry. Requiring only "the same final
answer" is too weak: it says nothing about a system that emits along the way, which is exactly
what a replayable service does.

The property has a name elsewhere. In language-based security it is *observational
determinism*: the attacker-visible behaviour of a concurrent program must not vary with the
scheduler (Roscoe 1995; Zdancewic and Myers 2003). Since it quantifies over pairs of runs it
is a 2-safety hyperproperty in the sense of Clarkson and Schneider (2010) rather than a trace
property. This work does not claim the property; it claims a criterion for when a
transactional discipline satisfies it, and a transfer theorem between implementations.

Second, "the same schedule" is not the right notion of sameness for schedules. Two runs may
differ in every operational detail — abort counts, snapshot choices, worker assignment — and
still be the same run semantically; conversely, two runs may happen to print the same output
for different semantic reasons. Fusing these notions is what makes the folklore look like a
list of unrelated rules. The model therefore needs a structural equivalence on schedules, not
an extensional one, and that equivalence is what carries the whole result.

## 3. The model M₀

M₀ is deliberately small: a body language over transactional cells, a journal, and an
execution discipline.

A **body** reads and writes cells, emits values, branches, and may invoke one further
primitive discussed below. Expressions read only locals. Every external observation is
factored through the cell interface, which is what makes the semantic universe closed: this
is not an assumption but the definition of the AST (`Body` in the mechanization), and Lemma 3B
is the demonstration of what breaks the moment the closure is pierced. A
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
assignment of logical time, and the journal that was consumed (`sem_forced`). It does not
carry abort counts, snapshot choices, worker allocation, or timing — and "does not carry" is
witnessed, not asserted: `abort_count_artifact` exhibits two legal runs of one `(P, J)` that
differ in an abort and agree in everything semantic. Two schedules are **semantically equivalent**,
written `S₁ ≈_J S₂`, when their semantic projections are equal.

## 4. Results

The five results form a ladder; each rung quantifies over strictly more than the one below.

```
            Seq(P, J) = fold(J)                  L1   one machine: none
                  │
                  ▼
            ordered commit + validation          L2   one machine, any schedule
            ⇒ Parallel = Seq
                  │
                  ▼
            boundary of safe observations        L3   any oracle over (journal,
            (preservation + counterexample)           logical time) — and no more
                  │
                  ▼
            semantic ⊊ observable ⊊ coincidence  L3.5 any legal trace
                  │
                  ▼
            substrate independence               L4   any machine satisfying
            (forced + refines)                        two interface laws
                  │
                  ▼
            failure refinement                   L5   any such machine,
            (forced weakened to a prefix)             now allowed to crash
```

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
are safe, and allocating a fresh cell by journal position is safe
(`safe_alloc_by_journal_position`). Allocation as such is not the problem.

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
- Two instances with disjoint vocabularies of artifacts are constructed:

  ```
                        Journal J
                       ┌────┴────┐
            optimistic │         │ wavefront (BSP)
                       ▼         ▼
      speculation,               static footprints,
      hostile snapshots,         waves of disjoint tx,
      validation, aborts         barrier merge, no aborts
                       │         │
                       └────┬────┘
                            ▼
                same Result, same Observable
          (artifacts: abort count | wave partition)
  ```
 The optimistic trace
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

**L5, failure refinement.** The interface of L4 assumes total substrates: `forced` demands
that a legal run consume the journal exactly. Real substrates crash. L5 weakens `forced` to a
*prefix* of the journal (`FailSoundSubstrate`) and proves that the price of the weakening is
exact: equality of observables becomes *prefix order* of observables, and nothing else is
lost. Concretely:

- `seq_out_prefix`: the reference fold is prefix-monotone — consuming a prefix of the journal
  emits a prefix of the reference observable. No machine is mentioned; this is why crashes can
  only truncate.
- `fail_substrate_independence`: for any two fail-sound substrates started identically on the
  same journal, projection-prefix order implies prefix order of the observables, *and* the
  longer run factors exactly through the shorter run's result: the continuation equals the
  sequential fold of the remaining journal from the crash state. Runs of different machines
  never diverge under partial failure — they only stop. The factorization clause is a strong
  form of recovery independence: any correct continuation is forced to factor through the
  crash state and the sequential semantics of the remainder, independently of the pre-crash
  schedule and even of which machine ran before the crash.
- `fail_observable_prefix`: crash-observable safety — the observable of any legal run is a
  prefix of `Seq(P, J)`'s. A crash may truncate output; it can never fabricate an observation
  that no sequential prefix would have produced.
- Conservativity: every sound substrate is fail-sound with the degenerate suffix
  (`SoundSubstrate.toFail`), and L4's conclusion is re-derived through the weaker interface
  (`substrate_independence_of_fail`). L4 is literally the total fragment of L5; no v1.0
  statement changed.
- Instance and strictness: the optimistic trace machine with one new legal event — halting
  mid-journal (`CrashRun`) — is fail-sound and strictly extends substrate 1
  (`runTrace_is_crashRun`). The witness `crash_prefix_witness` shows in one statement that the
  weakening is strict (the L4 `forced` law fails), that observable equality is genuinely lost,
  and that the prefix law is exactly what survives.

### Failure model

```
  total run    A B C D E F      Observable  o₁ o₂ o₃ o₄
  crashed run  A B C ×          Observable  o₁ o₂
                                            └────┬───┘
                                       a PREFIX, never a deviation:
                                       truncation is legal,
                                       fabrication is not
```

The failure model is deliberately minimal: **crash-stop between commits**. A substrate may
halt at any point between transactions; commits are atomic with respect to crashes (the
negative suite checks that a torn commit is caught). What L5 does *not* model: resumption of a
crashed run as one continued execution of one machine (recovery is an implementation and
liveness concern, kept outside X exactly as fairness was in L2), and any constraint on *where*
a substrate may crash — every prefix is admissible. The theorem is about what a crashed run
may have observed, not about what happens next.

## 5. Mechanization and witness

Everything above is mechanized in **Lean 4.31.0**, six self-contained files with no
dependencies, not even Mathlib, so that `lean Lemma5.lean` reproduces the top results on a
bare toolchain. There are **no `sorry`s**. The axiom footprint is checked rather than claimed:
CI compares the axioms of thirty headline theorems against a recorded list, so a proof that
starts depending on something new fails the build. `substrate_independence`,
`implements_M0_execute_eq`, `fail_substrate_independence_eq`, `runTrace_is_crashRun` and the
L1 theorems depend on no axioms at all; the rest use only `propext` and `Quot.sound`.

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
- **Phase D** is the experimental face of L5: both machines halt at random points (between
  transactions, or at a wave barrier), and every crashed run is checked against the four L5
  laws — the projection is a prefix of the journal, the result equals `Seq` of the consumed
  prefix, the emit stream is a prefix of the reference (no fabricated observations), and the
  sequential fold of the remainder resumed from the crash state lands exactly on `Seq(P, J)`.
- **The negative suite** breaks the substrates on purpose. Three structural breakages, commits
  out of journal order, an attempt counter leaked into the output, and two conflicting
  transactions fused into one wave, must be caught in 100% of cases, and so must the two crash breakages: a fabricated
  post-halt emit (in its sneaky variant it emits the *correct* next reference value, which
  the prefix law alone cannot see — only refinement against the consumed prefix can) and a
  torn commit. Five further breakages,
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

## 6. Related work

The full map, twenty-three works in six groups with the intersections spelled out, is in
[`RELATED_WORK.md`](RELATED_WORK.md). In brief.

*Known and used, not claimed.* Ordering the input log and executing deterministically as the
route to replication and replay (Schneider 1990; the deterministic database line from Calvin
2012 through BOHM, PWV, Aria and Spectrum). Optimistic execution with read-set validation
(Kung and Robinson 1981) and the serializability tradition around it (Papadimitriou 1979;
Bernstein, Hadzilacos and Goodman 1987). Implementation-independent specification of
transactional behaviour (Adya 1999; Cerone, Bernardi and Gotsman 2015). Correctness stated
against a sequential reference (Herlihy and Wing 1990; Guerraoui and Kapalka 2008). Refinement
as the proof shape (Abadi and Lamport 1991) and its mechanization for transactional systems
(VerIso 2025; C4 2022; the mechanized transactional-memory line). Determinism by construction
in languages, through static footprints (DPJ 2009) or monotone state (LVars 2013).

*Where this work differs.* The deterministic-database literature states the resulting rules as
guidance ("no clocks, no thread identifiers, no retry counters") without a criterion; the
security literature states the property but enforces it with a type system over a different
model; the mechanization literature verifies protocols one at a time against an isolation
level. What is assembled here is a two-sided criterion with a mechanized counterexample
(L3A/L3B), the strict separation of semantic from observable equivalence and from coincidence
(L3.5), and substrate independence as an interface theorem with two instances whose artifact
vocabularies are disjoint (L4).

Two neighbours are close enough to name rather than survey. Observational determinism is the
same property in a different setting, and any claim here must be relative to it. VerIso is
the closest mechanized work, and the comparison should be made after reading it in full
rather than from its abstract.

## 7. Limitations

Stated deliberately, because the value of the artifact depends on its boundary being visible.

- **No liveness.** M₀ says what a run may observe, never that a run terminates. The wavefront
  machine is total by construction (`wave_progress`), but progress under contention is not
  modelled.
- **No performance and no cost semantics.** The model has no notion of work, latency, or
  contention. Nothing here says that a substrate is fast, or even that it is faster than the
  sequential fold.
- **No scheduler optimality.** Wave partitioning is treated as an implementation artifact.
  Which partition to choose is outside the model.
- **No implementation engineering.** The substrates are models. There is no storage engine,
  no durability, no distribution. Failure is modelled (L5), but only as crash-stop between
  commits: resumption of a crashed run as a continued execution of one machine is not.
- **Granularity is not claimed.** The third side of the minimality triangle, the trade-off
  between transaction granularity and achievable parallelism, has experimental support only
  (fuzz runs in the research log; no theorem is stated, and none should be inferred).
- **Model scale.** Cells hold integers, bodies are finite, and the oracle is a pure function.
  The results are about the discipline, not about a production type system.

## 8. Future work

The natural next layer is **cost semantics**: attaching work to a run so that partitions and
schedules can be compared rather than merely declared equivalent. That brings in conflict
graphs, granularity as a formal parameter rather than an experimental observation, and a
performance model of the two substrates. Since it is a genuinely different pillar, it is
developed on a separate branch, leaving the safety story of v1.0 as a fixed reference point.

Beyond that: liveness and progress under contention; further weakenings of the interface,
of which L5's prefix law is the first — the natural next one is a projection coarser than a
list (quotient journals), with L5 as the template for "weaker law, exactly which weaker
conclusion"; an explicit recovery construction on top of the L5 factorization; and mapping the
boundary theorem onto an existing language's effect system to see how many of its primitives
fall on the allowed side.

## Artifact

`Topicspot/m0-semantics`, tag `v1.1` (v1.0 remains the frozen reference point of the safety
story). Lean sources in `lean/`, witness in `witness/`, full research log in
`docs/STATE_OF_PROJECT_v5.1.md`, the L5 decision record in `docs/NEXT_STAGE.md`.
`python scripts/verify.py` reproduces everything claimed here: build, absence of `sorry`,
axiom footprint, witness including phase D. The manifest of the reference run is committed as
`witness/run-v1.1.json` and attached to the release.
