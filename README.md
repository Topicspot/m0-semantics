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

Research, pre-publication. The mechanized part reaches Lemma 4 (substrate independence) in
Lean 4.31 with `0 sorry`; the only axioms used are `propext` and `Quot.sound`, and the core
`substrate_independence` theorem uses none.

| Layer | Content | State |
| --- | --- | --- |
| L1 | deterministic sequential fold | proved |
| L2 | ordered commit + validation ⇒ Parallel = Seq | proved |
| L3A / L3B | boundary of admissible extensions + `scheduleCounter` counterexample | proved |
| L3.5 | semantic ⊊ observable ⊊ coincidence | proved |
| L4 | substrate independence (`SoundSubstrate`, optimistic + wavefront instances) | proved |
| witness | `m0.py`, 106 000 randomized cases, 0 discrepancies | runs |

All layers are mechanized and present in [`lean/`](lean/).

Full witness run against the recovered mechanization (seed 2026): Phase A 40/40, Phase B and
Phase C 3 000 cases each with 0 discrepancies, negative mode `wrong_order` 317/317,
`schedule_counter` 400/400, `no_validation` 198/400.

The Lean sources were lost with the working chat and recovered the same day. The
mechanization is complete again — `Lemma1`, `Lemma2`, `Lemma3` (3A + 3B), `Lemma3_5`,
`Lemma4` — and every file was re-checked from scratch under Lean 4.31.0: compiles, `0 sorry`,
axiom footprint as documented, witness Phase A agreeing 100/100. See
[lean/README.md](lean/README.md) for the per-file report and
[docs/RECOVERY.md](docs/RECOVERY.md) for what happened.

## Layout

```
docs/     STATE_OF_PROJECT v5.1 (full research log, RU), recovery notes
lean/     the mechanization, Lemma1 … Lemma4 (Lean 4.31, no dependencies)
witness/  m0.py, the hostile differential witness
paper/    write-up outline
weave/    unrelated earlier project kept in this repo's history (see weave/README.md)
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
