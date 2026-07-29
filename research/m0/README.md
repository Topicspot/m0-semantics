# M₀ — deterministic state semantics

M₀ is a small formal model of *state that stays part of the protocol while the schedule does
not*. It targets systems where a replayed run must produce byte-identical observable output —
replicated state machines, deterministic simulations, matching engines, database kernels.

The property under study, informally:

> if two schedules are semantically equivalent for the same journal, the observable output of
> the run is identical

Formally `schedule₁ ≈_J schedule₂ ⇒ Observable(run₁) = Observable(run₂)`, with the reference
`Seq(P, J) = fold(J)`.

The model: transactional cells, optimistic execution against a snapshot, snapshot validation
at commit, commit strictly in journal order.

## Status

Research, pre-publication. The mechanized part reached Lemma 4 (substrate independence) in
Lean 4.31 with `0 sorry`; the only axioms used were `propext` and `Quot.sound`, and the core
`substrate_independence` theorem used none.

| Layer | Content | State |
| --- | --- | --- |
| L1 | deterministic sequential fold | proved |
| L2 | ordered commit + validation ⇒ Parallel = Seq | proved |
| L3A / L3B | boundary of admissible extensions + `scheduleCounter` counterexample | proved |
| L3.5 | semantic ⊊ observable ⊊ coincidence | proved |
| L4 | substrate independence (`SoundSubstrate`, optimistic + wavefront instances) | proved |
| witness | `m0.py`, 106 000 randomized cases, 0 discrepancies | runs |

Full witness run against the recovered mechanization (seed 2026): Phase A 40/40, Phase B and
Phase C 3 000 cases each with 0 discrepancies, negative mode `wrong_order` 317/317,
`schedule_counter` 400/400, `no_validation` 198/400.

The Lean sources were lost with the working chat and recovered the same day; `Lemma4.lean`
and `Lemma3_5.lean` are back in [`lean/`](lean/), re-verified from scratch (0 `sorry`, axioms
`propext` / `Quot.sound` only, `substrate_independence` axiom-free, Phase A 100/100). The
Lemma 3A/3B file with the `scheduleCounter` counterexample is still missing. See
[docs/RECOVERY.md](docs/RECOVERY.md) and [lean/README.md](lean/README.md).

## Layout

```
docs/     STATE_OF_PROJECT v5.1 (full research log, RU), recovery notes
lean/     mechanization — currently only the reconstruction plan
witness/  m0.py, the hostile differential witness
paper/    write-up outline
```

## Running the witness

Python 3.10+, standard library only.

```bash
python witness/m0.py b --n-b 2000      # parallel substrates vs reference
python witness/m0.py neg               # intentionally broken substrates must be caught
```

Expected: Phase B reports `0 discrepancies`; negative mode catches `wrong_order` and
`schedule_counter` in 100% of cases and `no_validation` in roughly half — the latter is not a
bug but the empirical face of observable coincidence from L3.5.

`python witness/m0.py a` additionally requires `lean` on `PATH`; it builds a harness on top of
`lean/Lemma4.lean` and differentially compares the Python reference interpreter against
`#eval runSeq`.

## What the witness is, and is not

`m0.py` is a falsification / validation witness, not a second proof. Agreement over millions
of cases raises confidence. A discrepancy is a counterexample to the implementation or to the
transcription of the specification — never to the theorem.

## License

Dual licensed under Apache-2.0 and MIT.
