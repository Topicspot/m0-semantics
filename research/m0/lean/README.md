# Mechanization

Lean 4.31.0, no dependencies (no Mathlib import): each file compiles standalone with
`lean Lemma4.lean`.

| Файл | Содержание |
| --- | --- |
| `Lemma4.lean` | 1 018 строк. Язык и эталонная семантика (`EvalBody`, `EvalSeq`, `runSeq`), детерминизм (`evalBody_det`, `seq_deterministic`), инструментированная семантика и валидация, оптимистический субстрат `RunTrace` с `trace_refines_seq` (содержание L2), волновой субстрат (`WaveOk`, `WaveRun`, frame-теорема `wave_refines_seq_aux`), интерфейс `SoundSubstrate` и `substrate_independence` (L4), свидетели `wave_partition_artifact`, `cross_substrate_witness`, полнота `SubstrateComplete` / `implements_M0_execute_eq`. |
| `Lemma3_5.lean` | 620 строк. Граница эквивалентности расписаний: структурная `≈_J` через `semProj`, `lemma3_5_equiv_implies_observable`, `same_journal_all_equiv`, строгость включений. |

Файлы восстановлены владельцем 29.07.2026 после потери чата (две присланные копии `Lemma4`
побайтово идентичны, md5 `8f8f9e80…`).

## Проверено в песочнице 29.07.2026

Lean 4.31.0, `lean Lemma4.lean` и `lean Lemma3_5.lean` — компилируются без ошибок и без
единого `sorry` (в файлах нет ни одного вхождения).

```
'substrate_independence'            does not depend on any axioms
'implements_M0_execute_eq'          does not depend on any axioms
'substrate_run_eq_seq'              depends on axioms: [propext]
'trace_refines_seq'                 depends on axioms: [propext, Quot.sound]
'wave_refines_seq'                  depends on axioms: [propext, Quot.sound]
'cross_substrate_witness'           depends on axioms: [propext, Quot.sound]
'wave_partition_artifact'           depends on axioms: [propext, Quot.sound]
'lemma3_5_equiv_implies_observable' depends on axioms: [propext, Quot.sound]
'same_journal_all_equiv'            depends on axioms: [propext, Quot.sound]
```

Совпадает с тем, что записано в State of Project v5.1: 0 `sorry`, только `propext` и
`Quot.sound`, ядро `substrate_independence` — без аксиом вообще.

Phase A витнесса против восстановленного файла: **100 кейсов, 100 совпадений, 0 расхождений**
(`python witness/m0.py a --n-a 100`, Lean-харнесс собирается поверх `lean/Lemma4.lean`).

## Чего по-прежнему нет

Отдельного файла с Lemma 3A / 3B — в частности с контрпримером `scheduleCounter`. В
`Lemma3_5.lean` он упоминается как канонический представитель класса, но его определения и
доказательства среди присланных файлов нет. Содержание Lemma 1 и Lemma 2 не потеряно: оно
воспроизведено внутри `Lemma4.lean` для расширенного языка (`seq_deterministic`,
`trace_refines_seq`).
