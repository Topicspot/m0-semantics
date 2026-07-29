# STATE OF PROJECT — M₀ / детерминированная семантика состояния
### 2026-07-09 (v5.1) · L4 принята; m0.py (differential witness) реализован и прогнан · этап механизации: L1 + L2 + L3A/L3B + L3.5 + L4 (substrate independence) закрыты машинно

## 1. Объект исследования

Класс систем, где **состояние — часть протокола**, а **порядок исполнения не должен быть частью протокола**: консенсус/RSM, детерминированные симуляции и игры, matching engines, детерминированные ядра БД, воспроизводимые сервисы. Канонический тезис:

> Существует класс систем, где детерминированное исполнение с немонотонным разделяемым состоянием является частью корректности протокола. Для этого класса нужна семантика, в которой расписание не является аргументом программы.

Ось проекта (единственная, споры «язык vs VM vs библиотека» закрыты): **closed semantic universe vs host language + convention**. Вопрос: минимальный замкнутый семантический объект, гарантирующий X структурой допустимых программ, а не дисциплиной.

## 2. Свойство X (канон)

- Сигнатура: execute(program, journal) = result, Result(P, J) = (State, Out); **Observable := projection(Result)** — граница X формулируется через Observable, не через внутренние состояния машины (механизировано: Observable r = r.2, emit-поток).
- Закон (safety property): schedule₁ ≈ schedule₂ ⇒ Observable(run(schedule₁)) = Observable(run(schedule₂)).
- Запрещённый источник наблюдаемого: **execution order** (единственный). Допустимые: journal, logical time, previous semantic state.
- Граница (теперь машинно, с двух сторон): **разрешено o = f(state, journal, logical_time)** — сохраняет X для всего класса расширений (Lemma 3A); **запрещено любое наблюдение, не являющееся функцией инвариантов семантического состояния**. Формальная формулировка (в нашем дискретном typed setting): observable must factor through semantic inputs (state, journal, logical_time). Запись observable ∉ σ(semantic inputs) — пояснительная σ-алгебраическая аналогия, Lean-модель σ-алгебру не измеряет. «schedule» — лишь конкретное представление execution relation; число спекулятивных попыток, latency, worker id, physical partition, cache state, GPU warp id — частные проявления того же класса, канонический представитель которого — scheduleCounter из Lemma 3B.

### 2.1 Semantic boundary refinement (после L3.5)

Structural schedule equivalence S₁ ≈_J S₂ определена НЕ через Observable, а через равенство семантической проекции расписания. semProj несёт: (1) commit-order; (2) logical time assignment (позиция в списке); (3) journal consumption (sem_forced). **Validation outcome НЕ закодирован в проекции** — он гарантируется легальностью трассы (RunTrace.commit : validates …), т.е. принадлежит admissibility-отношению, а не проекции. Для substrate independence это означает: второй субстрат обязан доказывать тот же admissibility-инвариант (в L4 это закон refines интерфейса SoundSubstrate), а не «та же проекция содержит валидацию». Всё остальное — implementation artifacts:


abort count, speculative order,        journal position, commit order,
snapshot choice, worker assignment,    logical time; validation — через
allocation timing                      admissibility (легальность трассы)
        = implementation artifacts            = semantic artifacts


Машинно (Lemma3_5.lean): ≈_J ⇒ Observable₁ = Observable₂ (семантический уровень); все легальные прогоны одного (P, J) попарно ≈_J (same_journal_all_equiv; точная формулировка следствия: любая компонента трассы, не сохраняемая semProj, наблюдательно нерелевантна для X и принадлежит слою реализации — «все различия суть implementation artifacts» было бы метаутверждением о классификации, сильнее доказанного; abort_count_artifact — явный свидетель); обратное НЕВЕРНО: ¬(S₁ ≈_J S₂) ⇏ Observable₁ ≠ Observable₂ (observable_coincidence_not_equiv). Иерархия строгая:


semantic equivalence  ⊊  observable equivalence  ⊊  implementation coincidence


Schedule equivalence — инвариант для substrate independence: тезис не «этот конкретный M₀ переносится», а «любой substrate, реализующий тот же semantic closure, есть реализация M₀». **После L4 этот тезис — теорема** (см. §2.2).

### 2.2 Substrate independence (после L4)

«Реализует semantic closure» формализовано как интерфейс SoundSubstrate: субстрат — произвольный тип расписаний Sched, отношение легальных прогонов Run и семантическая проекция proj : Sched → List TxId с двумя законами: (i) forced — проекция легального прогона равна потреблённому журналу; (ii) refines — каждый легальный прогон рафинирует последовательную свёртку своей проекции. Это ≈_J из L3.5, поднятое с одной машины до интерфейса: проекция — весь семантический контент расписания, внутренний словарь событий машины не ограничен.

**Нецикличность интерфейса (обязательная проверка рецензента перед v5 — выполнена).** SoundSubstrate минимален и НЕ содержит спрятанного равенства execute = Seq(P,J). Поля: Sched (тип трасс), Run (admissibility-отношение конкретной машины: у оптимистической — динамическая валидация, у wavefront — статический WaveOk), proj, и два закона: forced : Run → proj sc = J и refines : Run → EvalSeq E P s o (proj sc) s' o' — где EvalSeq — *отношение* последовательного вычисления собственной проекции, а не равенство с Seq(P,J). Равенство Result = Seq(P,J) — производная теорема substrate_run_eq_seq = refines + forced + seq_deterministic + runSeq_sound; содержательная нагрузка лежит в неинтерфейсных доказательствах экземпляров (trace_refines_seq через валидацию L2, wave_refines_seq через frame-теорему). Структура ровно та, которую требует ревью: Definitions → laws (admissibility, projection, sound, complete) → Theorem (ImplementsM₀ A → executeA = Seq → executeA = executeB).

Машинно (Lemma4.lean): substrate_independence — для ЛЮБЫХ двух sound-субстратов равенство проекций ⇒ равенство Result (тем более Observable); substrate_run_eq_seq — каждый легальный прогон на каждом sound-субстрате равен Seq(P,J): **M₀ задаётся классом субстратов, удовлетворяющих одной и той же semantic closure specification; эквивалентность субстратов — следствие (executeA = Seq = executeB), а не заранее заданное отношение**. Два не-тривиально разных представителя внутри Lean:


Substrate 1 (optimistic, L3.5):        Substrate 2 (wavefront, L4, НОВЫЙ):
спекуляции, враждебные снапшоты,       статический конфликт-анализ по
динамическая валидация, ordered        синтаксическим футпринтам, BSP-волны
commit; аборты возможны                попарно неконфликтующих tx против
                                       общего состояния входа волны, merge
артефакты: abort count,                на барьере; ни снапшотов, ни
snapshot choice                        валидации, ни абортов
                                       артефакты: разбиение на волны


Субстанция субстрата 2 — wave_refines_seq_aux: frame-теорема о невмешательстве (дизъюнктность статических футпринтов ⇒ исполнение всей волны против её входного состояния реализует последовательную свёртку), выведенная из ядра snapshot adequacy L2: read-set тела лежит в его футпринте (runInstr_rs_cells), записи не выходят из футпринта (runInstr_writes_frame). wave_progress / trace_progress — completeness обоих субстратов: SubstrateComplete (для каждого (s,o,J) существует легальный прогон) — реализуемость существованием, сознательно НЕ liveness: интерфейс не требует, чтобы каждое легальное расписание терминировало (бесконечные attempt-циклы остаются легальными), иначе в X протекла бы liveness. Свидетели: wave_partition_artifact — разбиение на волны есть implementation artifact (одна параллельная волна [0,1] vs две последовательные [[0],[1]], проекции равны, Result равны) — точный аналог abort_count_artifact субстрата 1; cross_substrate_witness — сквозной: оптимистический прогон С АБОРТОМ и однoволновой параллельный прогон wavefront-машины дают идентичный Result. Две машины, два непересекающихся словаря артефактов, одна семантика.

## 3. Модель M₀ (заморожена)

Транзакционные ячейки; оптимистическое параллельное исполнение (спекуляции, аборты, ре-исполнения); фиксация строго в порядке журнала, только с валидным снапшотом; emit — единственный вывод; request(id) — внешние значения через журнал. Референс-семантика: Seq(P,J) = fold(J) — immutable log есть денотационная модель, ячейки — операционная оптимизация её параллельного вычисления.

**О «чистоте» тел (уточнённая формулировка):** purity is **derived from the semantic closure of the object language**, не постулируется. В механизации: выражения читают только локали; вся внешняя наблюдаемая память факторизована через операцию read (ячейки) и ext (журнал/логическое время); следовательно runInstr — тотальная функция от (σ, body). Это более сильное утверждение, чем «чистота доказана»: это и есть определение закрытой семантической вселенной. Следствие: clock(), random(), network(), произвольный allocator() невозможно «добавить позже» без изменения языка — что и демонстрирует Lemma 3B. На возражение «вы доказали чистоту, потому что запретили нечистоту в AST» ответ канонический: **да, именно это является определением X**.

**Каноническая формулировка о ячейках (усилена против атак):** не «транзакционные ячейки — минимальная форма состояния», а: **«транзакционные ячейки — минимальная операционная структура, реализующая X внутри класса закрытых порядко-чувствительных семантик при сохранении параллелизма»** (минимальность — пока гипотеза, см. §5 треугольник).

## 4. Статус атак

| Атака | Статус | Итог |
|---|---|---|
| I (det-VM) | закрыта | Move/EVM/det-WASM — родственники; критерий — замкнутость семантической вселенной |
| J (CRDT/actors/log/STM) | закрыта; после L2 существенно ослабла | CRDT — другой класс (order independence); actors — большая ячейка или реинвент транзакций; log — наша же денотационная база; STM без det-порядка неполон. L2 добавляет: корректен ЛЮБОЙ планировщик при validation + ordered commit — теорема о классе реализаций, не о механизме |
| K (библиотека) | **переформулирована (точная версия)** | НЕ «библиотека невозможна», а: **обычный API-слой поверх host-языка не обеспечивает X автоматически; контрпримеры возникают при сохранении host-модели вычисления** (Q3: 343/800 нарушений при 100% легальном API). Библиотека даёт ∀ terms ∈ library universe → X — а это уже закрытая вселенная, т.е. сам семантический объект |

## 5. Статусы утверждений

- **Доказано машинно (Lean 4.31, 0 sorry, аксиомы только propext/Quot.sound):**
  - **Lemma 1** (deterministic fold) — Lemma1.lean (straight-line), передоказана для AST с ветвлением в Lemma2.lean и для расширенного языка в Lemma3.lean;
  - **Lemma 2** (commit-order) — Lemma2.lean: ordered commit + validation + closure ⇒ Parallel(P,J) = Seq(P,J) при **произвольных (в т.ч. злонамеренных) снапшотах**; safety безусловна (par_refines_seq), существование конструктивно (par_progress); fairness сознательно не формализован (свойство реализации, не X). Ключ: runInstr_snapshot_adequate — read-set agreement ⇒ same execution, включая control flow (ite);
  - **Lemma 3A** (extension preservation) — Lemma3.lean: для ЛЮБОГО примитивного эффекта E : Q → TxId → Int (функция запроса и логического времени — schedule-инвариантность по построению типа) расширенная семантика сохраняет X. Lemma 2 — вырожденный случай Q = Empty. Следствие safe_alloc_by_journal_position: **аллокация сама по себе X не ломает** — newcell(id := h(journal_position)) безопасен;
  - **Lemma 3B** (boundary counterexample) — Lemma3.lean: примитив scheduleCounter (машина со счётчиком попыток; ordered commit и validation сохранены!) даёт два легальных расписания с разными Observable: ∃ e₁ e₂: schedule(e₁) ≠ schedule(e₂) ∧ Observable(e₁) ≠ Observable(e₂);
  - **Необходимость условий (2 из 3 сторон треугольника + разделение Validation/Order):** order_necessary — валидация без порядка ⇒ недетерминированный исход; validation_necessary — порядок без валидации ⇒ lost update (результат ≠ Seq). Условия ValidationCorrectness и OrderCorrectness тем самым разделены: каждое необходимо по отдельности, вместе достаточны (L2).
- **Экспериментально подтверждено (фальсификация, НЕ доказательство):** X на fuzz-классе (90k прогонов, 0 нарушений); Q2d — state-dependent allocation безопасна при virtual-time идентичности (теперь покрыто L3A); Q2e — request-через-журнал безопасен, unlogged effects ломают (теперь покрыто L3A/L3B); Q3 — host-побег ломает X при легальном API; гранулярность: aborts/commit blob-vs-cells 3.2×→5.5×.
- **Lemma 3.5** (schedule equivalence boundary) — Lemma3_5.lean, машинно, для всего расширенного класса языков из 3A: расписание реифицировано как трасса событий (attempt/commit со снапшотами); semProj — структурная семантическая проекция; sem_forced (journal consumption форсирован дисциплиной машины); lemma3_5_equiv_implies_observable; same_journal_all_equiv; abort_count_artifact; observable_coincidence_not_equiv. См. §2.1.
- **Lemma 4** (substrate independence) — Lemma4.lean, машинно: SoundSubstrate, optimisticSubstrate/wavefrontSubstrate как его экземпляры, substrate_independence, substrate_run_eq_seq, wave_refines_seq_aux (frame-теорема), wave_progress, wave_partition_artifact, cross_substrate_witness; после ревью L3.5 добавлено: SubstrateComplete, trace_progress, optimistic_complete, wavefront_complete, implements_M0_execute_eq (sound+complete = ImplementsM₀ в смысле рецензента; completeness — экзистенциальная реализуемость, НЕ liveness). См. §2.2.
- **Переименование (вместо «треугольника минимальности»): Safety theorems + scalability conjecture.** Стороны (1) и (2) — теоремы о *необходимости корректности* (without ordered commit → not X; without validation → not X). Утверждение (3) — НЕ необходимость корректности, а необходимость для *класса производительности* (without granularity → no parallel speedup), другой логический уровень. Статус (3): только эмпирика (J1); как теорема потребует отдельной cost semantics: Parallelism = f(conflict graph, granularity, scheduler, cost) — semantics + resource model, в текущей модели теоремой НЕ обещается. Также открыты альтернативные пути к X: det-dataflow / incremental / partial-order / conflict-free decomposition.
- **Открытые вопросы:** третья сторона треугольника; LVars-пробел (монотонные подъязыки); точная граница «эквивалентности расписаний»; перф-модель; бесконечные тела (текущие модели — конечные тела, то же условие завершимости, что в бумажной версии).

## 6. Что заморожено

Никаких расширений модели: без capability system, ownership, компилятора, оптимизатора, рантайма, экосистемы, тулинга, имени. Только доказательная база.

## 7. Дорожная карта лемм

1. **Lemma 1 (Deterministic fold)** — ✅ машинно.
2. **Lemma 2 (Commit-order theorem)** — ✅ машинно (усиленная форма: произвольный снапшот, ∀scheduler).
3. **Lemma 3 (Boundary theorem)** — ✅ машинно в разбивке 3A (preservation schema) + 3B (counterexample через primitive effect, не через allocator).
4. **Lemma 3.5 (Schedule equivalence boundary)** — ✅ машинно: структурное ≈_J, разделение semantic / observable / coincidence, артефакты реализации отделены от семантических артефактов.
5. **Lemma 4 (Substrate independence)** — ✅ машинно (Lemma4.lean, Lean 4.31, 0 sorry, propext/Quot.sound; ядро substrate_independence — вообще без аксиом): интерфейс SoundSubstrate (forced + refines = semantic closure), второй субстрат (wavefront/BSP со статическим конфликт-анализом) как машина внутри Lean, кросс-субстратная теорема через ≈_J, свидетели wave_partition_artifact и cross_substrate_witness.

### 2.3 m0.py — внешний враждебный исполнитель (статус: реализован)

Роль зафиксирована ревью: **falsification / validation witness, не третье доказательство**. Совпадение на миллионах случаев усиливает доверие; расхождение — контрпример к реализации или к транскрипции спецификации, не к теореме. Архитектура по фазам рецензента:

- **Phase A** — генератор случайных AST-программ + чистый последовательный интерпретатор; дифференциальная сверка python_seq == Lean #eval runSeq (питон против ФАКТИЧЕСКОГО Lean-определения: генерируется Lean-файл с кейсами поверх Lemma4.lean и исполняется lean).
- **Phase B** — параллельный генератор трасс (attempt/snapshot/abort/commit) + wavefront-генератор со случайными разбиениями и случайными worker-перестановками внутри волны; чекер на каждой трассе: forced (proj==J), sound (result==Seq(P,J)), observable (emit==reference), независимый replay admissibility-правил, кросс-субстратное сравнение.
- **Phase C** — adversarial fuzzing: враждебные снапшоты (85% порчи), abort storms, искусственные задержки, случайные перестановки работников.
- **Negative mode** — намеренно сломанные субстраты: wrong commit order, missing validation, scheduleCounter-инъекция в observable; чекер обязан их ловить (positive: valid substrates survive / negative: known violations fail).

Результаты прогонов (2 сида): Phase A — 100/100 кейсов совпали с Lean #eval runSeq; Phase B+C — 106 000 случайных (P, J, s₀), 0 расхождений, ~580 000 абортов суммарно, кросс-субстратные сравнения на каждом кейсе; negative mode — wrong order 1851/1851 пойман, scheduleCounter 2400/2400 пойман, missing validation ~49.5% (см. ниже).

Замечание к negative mode: missing validation ловится не в 100% случаев — это ОЖИДАЕМО и является эмпирической иллюстрацией observable coincidence из L3.5 (враждебный снапшот, чьи испорченные ячейки не читаются телом, даёт совпадающий результат); wrong order и scheduleCounter ловятся в 100%.

**Следующий этап:** (1) ~~внешний субстрат — интерпретатор m0.py~~ ✅ реализован (m0.py) с дифференциальным тестированием против Lean-модели (эмпирический витнесс substrate independence в исходном смысле; Lean-теорема L4 задаёт спецификацию, которой он обязан удовлетворять); (2) granularity — как scalability-исследование с отдельной cost semantics, без обещания теоремы в текущей модели. Замечание после L4: wavefront-субстрат — это одновременно первый шаг к granularity (статический конфликт-граф уже формализован через футпринты и DisjCells; cost semantics сможет строиться поверх WaveOk-разбиений: ширина волны = доступный параллелизм).

*Конец State of Project.*
