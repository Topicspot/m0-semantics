# Related work: map of intersections

Purpose of this file: state what is already known, and where M₀ begins. Not to argue novelty.

Method and its limits: the entries below were selected by topic, and each was checked against
the paper itself or its abstract and published venue. Full texts were not read end to end, so
every claim in the "establishes" column is at the granularity of the main result, and the
"difference" column is a hypothesis to be confirmed while writing the paper, not a verdict. A
row marked **⚠ read in full** is one where the overlap is close enough that reading the whole
paper is required before any novelty claim is made.

---

## 1. Concurrency control and serializability theory

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Papadimitriou, *The serializability of concurrent database updates*, JACM 1979 | Formal theory of serializable histories; deciding serializability of a history is NP-complete | The idea that a correct concurrent execution is one equivalent to some serial one | Equivalence is to *some* serial order; M₀ fixes the order externally (the journal) and asks about the observable, not about the existence of an equivalent order |
| Kung and Robinson, *On optimistic methods for concurrency control*, TODS 1981 | Optimistic execution with a read-set validation phase; correctness argument for validation | The optimistic substrate of M₀ is this algorithm: speculate, validate, commit | Their correctness target is serializability; M₀'s is equality with a *specific* fold and equality of emitted output, and the discipline is proved sufficient mechanically |
| Bernstein, Hadzilacos and Goodman, *Concurrency Control and Recovery in Database Systems*, 1987 | The standard framework: histories, conflict serializability, scheduler correctness proofs | The vocabulary of read sets, write sets, commit order | Pen-and-paper, no mechanization, no notion of an emitted observable stream, no cross-substrate statement |
| Adya, *Weak Consistency*, MIT PhD thesis 1999 | Implementation-independent specification of isolation levels via dependency graphs | The explicit goal of specifying behaviour without reference to an implementation | Adya characterises *which anomalies* a level permits; M₀ characterises *which observations a program may make* without breaking replay |
| Cerone, Bernardi and Gotsman, *A framework for transactional consistency models with atomic visibility*, CONCUR 2015 | Axiomatic, declarative framework for transactional consistency models | Declarative specification independent of the machine | Consistency of visibility between transactions, not schedule-independence of the observable output |

## 2. Deterministic transaction processing

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Thomson et al., *Calvin*, SIGMOD 2012 | A deterministic database: agree on a log of transactions first, then execute so the result is equivalent to the log order | This *is* the engineering shape of M₀: ordered journal, execution must not deviate from it | Calvin is a system with performance results; the discipline is argued informally and there is no theorem about which primitives keep the guarantee |
| Faleiro and Abadi, *Rethinking serializable multiversion concurrency control* (BOHM), VLDB 2015 | Deterministic MVCC where versions are assigned before execution | Ordering decided before execution; artifacts of execution must not leak | Engineering; correctness by construction of the algorithm rather than a criterion over programs |
| Faleiro, Abadi and Hellerstein, *High performance transactions via early write visibility* (PWV), VLDB 2017 | Writes made visible before commit while preserving determinism | Precisely the kind of substrate M₀'s interface is meant to cover | No formal interface; the argument is specific to this algorithm |
| Lu, Yu, Cao, Madden, *Aria*, VLDB 2020 | Deterministic OLTP without knowing read/write sets in advance: batch execution then deterministic reservation/commit | Batch-wise execution against a fixed snapshot, close in shape to M₀'s wavefront substrate | Performance-oriented; no proof that its schedule freedom is unobservable, and no statement transferring between substrates |
| Abadi and Faleiro, *An overview of deterministic database systems*, CACM 2018 | Survey: sources of non-determinism, why determinism buys replication and replay | Names exactly the folklore M₀ formalises (no clocks, no thread ids, no timing) | A survey of practice; the boundary is stated as guidance, not as a theorem with a counterexample |
| Zhang et al., *Spectrum*, VLDB 2024 | Speculative deterministic concurrency control for smart contract ledgers | Speculation plus a fixed order, same contract as M₀ | Systems paper; determinism assumed as a requirement, not characterised |

## 3. Correctness conditions and their mechanization

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Herlihy and Wing, *Linearizability*, TOPLAS 1990 | Correctness condition for concurrent objects: equivalence to a sequential execution respecting real time | Correctness stated as agreement with a sequential reference | Real-time order is the reference; M₀'s reference is a journal, and real time is explicitly not observable |
| Guerraoui and Kapalka, *On the correctness of transactional memory*, PPoPP 2008 | Opacity: even aborted transactions must see consistent state | Aborted attempts are constrained but must remain unobservable | Opacity constrains what a *doomed* transaction may read; M₀ says the number and content of attempts must not reach the output |
| Lesani, Palsberg, Millstein and others, mechanized TM correctness (I/O automata, PVS; *Putting opacity in its place*, 2012 and later) | Machine-checked proofs that specific TM algorithms satisfy opacity | Mechanized correctness of a concurrency discipline | Per-algorithm verification against opacity; no interface-level theorem quantifying over substrates |
| Lesani, Bell, Chlipala et al., *C4: verified transactional objects*, OOPSLA 2022 | Coq framework for verified transactional objects with composable proofs | Mechanized, and about transactional execution | Concerns object libraries and their composition, not journal-ordered replay determinism |
| **Rad, Basin et al., *VerIso*, VLDB 2025** ⚠ read in full | Isabelle/HOL framework proving that concrete protocols (for example strict 2PL) refine abstract isolation models, by refinement | Mechanized refinement between a concrete protocol and an abstract semantics, in a proof assistant, for database transactions | Their abstract models are isolation levels; M₀'s abstract model is the sequential fold plus an observable, and the headline result is independence across substrates rather than a per-protocol refinement. This is the closest neighbour in the mechanized direction and must be read fully |

## 4. Refinement, simulation and verified systems

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Abadi and Lamport, *The existence of refinement mappings*, TCS 1991 | When a low-level specification can be proved to implement a high-level one, with history and prophecy variables | M₀'s `SoundSubstrate.refines` is a refinement obligation of exactly this kind | The general theory of refinement; M₀ instantiates it and adds the transfer theorem between two refinements of the same abstract object |
| Schneider, *Implementing fault-tolerant services using the state machine approach*, ACM Computing Surveys 1990 | Replication requires replicas to be deterministic state machines fed the same ordered input | The contract M₀ formalises, stated as a requirement | Determinism is an *assumption* on the state machine; M₀ asks what makes that assumption true for a language with speculation |
| Wilcox et al., *Verdi*, PLDI 2015 | Coq framework for verified distributed systems, verified system transformers, verified Raft | Machine-checked correctness with a sequential specification as the reference | Concerns network faults and consensus; execution inside a node is not the subject |
| Hawblitzel et al., *IronFleet*, SOSP 2015 | Practical distributed systems proved correct by refinement from a TLA-style state machine | Refinement to a state machine specification, machine-checked | Whole-system verification effort; no reusable criterion about which primitives are safe |

## 5. Deterministic execution, replay and testing

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Aviram et al., *Determinator*, OSDI 2010; Bergan, Hunt, Ceze and Gribble, *Deterministic process groups in dOS*, OSDI 2010 | OS-enforced deterministic parallel execution; nondeterminism is confined by construction | The same goal: the schedule must not be observable | Achieved by runtime enforcement with a cost; no characterisation of which language primitives are safe |
| O'Callahan, Jones, Froyd, Huey, Noll and Partush, *Engineering record and replay for deployability* (rr), USENIX ATC 2017 | Practical low-overhead record and deterministic replay of native programs | Replay as a first-class requirement | Records the nondeterminism instead of excluding it; the recording is exactly what M₀ forbids programs to observe |
| FoundationDB simulation testing (FoundationDB paper, SIGMOD 2021) | A single-threaded deterministic simulator finds distributed bugs reproducibly | Determinism used as an engineering instrument, and a differential-testing culture close to this project's witness | Testing methodology, no formal criterion |
| Kokologiannakis and Vafeiadis, *GenMC*, CAV 2021 | Stateless model checking modulo weak memory: explore all executions up to equivalence | Quotienting executions by an equivalence and checking that the observable does not vary across a class | GenMC decides per program by exhaustive search; M₀ proves the quotient once, for all programs in the language, and the equivalence is the object of the theorem rather than a search optimisation |

## 6. Deterministic parallelism in programming languages

| Work | Establishes | Overlap with M₀ | Difference |
| --- | --- | --- | --- |
| Bocchino et al., *A type and effect system for Deterministic Parallel Java*, OOPSLA 2009 | A type and effect system guaranteeing that a parallel program is deterministic | Static footprints, disjointness, non-interference: the same argument as M₀'s wavefront substrate | Determinism is guaranteed by typing at compile time; M₀ assumes no type system and covers speculative substrates where footprints overlap dynamically |
| Marlow, Newton and Peyton Jones, *A monad for deterministic parallelism*, Haskell 2011 | A parallel programming API deterministic by construction | Determinism as a language-level guarantee | Determinism of a pure dataflow computation, no journal, no shared mutable state, no commit order |
| Kuper and Newton, *LVars*, FHPC 2013 (and *Freeze after writing*, POPL 2014) | Deterministic and quasi-deterministic parallel programming with monotone shared state | Monotone structure making schedule order unobservable | The unobservability comes from lattice monotonicity; M₀'s comes from ordered commit plus validation, and permits overwriting |
| **Zdancewic and Myers, *Observational determinism for concurrent program security*, CSFW 2003**; Roscoe, *CSP and determinism in security modelling*, IEEE S&P 1995 ⚠ read in full | Security definition: the low-visible behaviour of a concurrent program must be identical under all schedules | The *property* is the same shape as X: observable behaviour independent of the schedule | Their setting is information flow, the quantification is over attacker-visible traces, and the aim is a type system enforcing the property. M₀ fixes a transactional discipline and proves the property holds, then transfers it across substrates. The framing overlap is real and must be acknowledged explicitly |
| Clarkson and Schneider, *Hyperproperties*, JCS 2010 | Properties over *sets* of traces; 2-safety and why such properties are not trace properties | Property X quantifies over pairs of runs, so it is a 2-safety hyperproperty | Provides the classification and the verification theory, not the concrete criterion for a transactional language |

---

## What is known, and where M₀ begins

**Known, and not claimed here.** That ordering the input log and executing deterministically
gives replay and replication (Schneider; Calvin and the deterministic database line). That
optimistic execution with read-set validation is correct (Kung and Robinson; the whole
serializability tradition). That a correctness condition should be stated against a sequential
reference (Herlihy and Wing; Adya; Cerone et al.). That refinement is the right proof shape
(Abadi and Lamport) and that it can be mechanized for transactional protocols (VerIso, C4,
the TM verification line). That a property of the form "the observable does not depend on the
schedule" exists and has a name in security: observational determinism (Zdancewic and Myers;
Roscoe), classified as a 2-safety hyperproperty (Clarkson and Schneider). That static
footprint disjointness gives deterministic parallelism (DPJ), as does monotone shared state
(LVars).

**Where M₀ starts.** Three things appear not to be assembled anywhere in this form.

1. **A criterion, with both sides.** L3A says every oracle of type `Q → TxId → Int`, that is
   every observation factoring through the journal position, preserves the property, for an
   arbitrary query type. L3B exhibits an oracle that observes the execution relation and
   breaks it. The deterministic database literature states the resulting *rules* (no clocks,
   no thread ids, no retry counters); the security literature states the *property* but
   enforces it with a type system on a different language model. The general statement that
   these rules are one class, with an explicit boundary and a mechanized counterexample, is
   the first candidate contribution.
2. **The strictness of the three levels.** Semantic equivalence ⊊ observable equivalence ⊊
   coincidence, each inclusion strict and witnessed. Observational determinism is usually
   defined extensionally, over observable traces; separating structural equivalence from
   accidental agreement of outputs, and proving the separation, is the second candidate.
3. **Substrate independence as an interface theorem.** Two laws, `forced` and `refines`, are
   enough: any two substrates satisfying them agree on the observable whenever their semantic
   projections agree, and both an optimistic and a wavefront machine are instances. The
   literature verifies protocols one at a time; quantifying over substrates and instantiating
   with two machines whose artifact vocabularies are disjoint (abort counts versus wave
   partitions) is the third candidate, and the one that looks most defensible.

**Honest risk.** The framing overlap with observational determinism is close enough that the
paper must cite it in the first two pages rather than in a survey at the end, and the
mechanization overlap with VerIso must be measured by reading it in full. Neither is a
duplicate of the L4 statement as far as the abstracts show, but "as far as the abstracts show"
is the correct strength for this file today.

## Effect on the next stage

Two adjustments to the plan follow from the survey.

- The extended abstract should motivate through the folklore-to-criterion move and name
  observational determinism explicitly, instead of implying the property is new.
- Cost semantics is not the only candidate for the next stage. Granularity has an established
  neighbour in DPJ-style effect systems, so the more distinctive direction may be to push the
  substrate interface further: a substrate with partial failure, or a substrate whose
  projection is coarser than a list, which is where the current `forced` law would have to be
  weakened.
