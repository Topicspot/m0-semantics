# Mechanization

Lean 4.31.0, no dependencies (no Mathlib): every file is standalone and compiles on its own
with `lean Lemma4.lean` and so on. The files are cumulative — each later file re-derives what
it needs from the earlier layers rather than importing it, so `Lemma4.lean` alone contains the
whole chain up to substrate independence.

| Файл | Строк | Содержание |
| --- | --- | --- |
| `Lemma1.lean` | 155 | Язык и эталонная семантика (`EvalBody`, `EvalSeq`), детерминизм `Seq`: `evalBody_det`, `lemma1_seq_deterministic`, исполнимая версия `runSeq` и её адекватность (`runSeq_sound`, `seq_unique_result`). |
| `Lemma2.lean` | 550 | Инструментированная семантика: read-set, снапшот, `validates`, `runInstr_snapshot_adequate`, `commit_step`/`commit_evalBody` и главный результат — `par_refines_seq` (упорядоченный коммит + валидация ⇒ Parallel = Seq). |
| `Lemma3.lean` | 678 | Граница допустимых расширений. `lemma3A_extension_preservation` — для любого типа запросов `Q`, чьи ответы зависят от журнала, а не от расписания, свойство сохраняется. `lemma3B_boundary_counterexample` — контрпример `scheduleCounter`. Плюс леммы необходимости: `order_necessary`, `validation_necessary`, `par_progress`. |
| `Lemma3_5.lean` | 620 | Граница эквивалентности расписаний: структурная `≈_J` через `semProj`, `lemma3_5_equiv_implies_observable`, `same_journal_all_equiv`, строгость включений semantic ⊊ observable ⊊ coincidence. |
| `Lemma4.lean` | 1 018 | Независимость от субстрата: интерфейс `SoundSubstrate`, два инстанса (оптимистический трассовый и волновой), frame-теорема `wave_refines_seq`, `substrate_independence`, свидетели `wave_partition_artifact` и `cross_substrate_witness`, полнота `implements_M0_execute_eq`. |

## Проверено в песочнице 29.07.2026

Все пять файлов компилируются Lean 4.31.0 без ошибок (1.5–2.2 с каждый) и не содержат ни
одного `sorry`.

```
lemma1_seq_deterministic          does not depend on any axioms
seq_unique_result                 does not depend on any axioms
runSeq_sound                      does not depend on any axioms
substrate_independence            does not depend on any axioms
implements_M0_execute_eq          does not depend on any axioms
lemma3B_boundary_counterexample   depends on axioms: [propext]
validation_necessary              depends on axioms: [propext]
substrate_run_eq_seq              depends on axioms: [propext]
par_refines_seq                   depends on axioms: [propext, Quot.sound]
commit_evalBody                   depends on axioms: [propext, Quot.sound]
lemma3A_extension_preservation    depends on axioms: [propext, Quot.sound]
order_necessary                   depends on axioms: [propext, Quot.sound]
par_progress                      depends on axioms: [propext, Quot.sound]
trace_refines_seq                 depends on axioms: [propext, Quot.sound]
wave_refines_seq                  depends on axioms: [propext, Quot.sound]
cross_substrate_witness           depends on axioms: [propext, Quot.sound]
wave_partition_artifact           depends on axioms: [propext, Quot.sound]
lemma3_5_equiv_implies_observable depends on axioms: [propext, Quot.sound]
same_journal_all_equiv            depends on axioms: [propext, Quot.sound]
```

Совпадает с тем, что записано в State of Project v5.1: 0 `sorry`, только `propext` и
`Quot.sound`, ядро (`substrate_independence`, L1) — без аксиом вообще.

Phase A витнесса против этих файлов: **100 кейсов, 100 совпадений, 0 расхождений**
(`python witness/m0.py a --n-a 100`, харнесс собирается поверх `lean/Lemma4.lean`).

Файлы восстановлены владельцем 29.07.2026 после потери рабочего чата; две присланные копии
`Lemma4` побайтово идентичны (md5 `8f8f9e80…`). Потерь в механизации нет.
