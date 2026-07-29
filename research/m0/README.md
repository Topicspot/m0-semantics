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

**The Lean sources are currently missing** — see [docs/RECOVERY.md](docs/RECOVERY.md). This
repository exists so that the surviving artifacts stop living in a chat log. Everything needed
to re-derive the mechanization is in [lean/RECONSTRUCTION.md](lean/RECONSTRUCTION.md).

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

`python witness/m0.py a` additionally requires `lean` on `PATH` and `witness/Lemma4.lean`; it
is disabled until the mechanization is restored.

## What the witness is, and is not

`m0.py` is a falsification / validation witness, not a second proof. Agreement over millions
of cases raises confidence. A discrepancy is a counterexample to the implementation or to the
transcription of the specification — never to the theorem.

## License

Dual licensed under Apache-2.0 and MIT.
