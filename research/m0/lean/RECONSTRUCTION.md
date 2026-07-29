# Реконструкция механизации

Оригинальные `Lemma1..4.lean` утеряны (см. [`../docs/RECOVERY.md`](../docs/RECOVERY.md)).
Этот файл — всё, что о них известно достоверно: сигнатуры, имена и семантика, извлечённые из
двух независимых источников — текста State of Project v5.1 и кода `witness/m0.py`, который
писался как построчное зеркало Lean-определений («The language, the instrumented semantics and
both machines mirror Lemma4.lean §0–§6 definition-for-definition, same names in comments»).

Ничего в этом файле не додумано. Там, где источник даёт только имя без тела, так и написано.

## 1. Поверхностный API (достоверно — из генератора Phase A)

Phase A витнесса дописывала кейсы поверх `Lemma4.lean` и исполняла `lean`. Значит эти
определения существовали ровно с такими именами и типами:

```lean
-- типы
State    -- String → Int   (в кейсах: fun c => if c = "c0" then (…: Int) else … else 0)
Out      -- List Int
Journal  -- List TxId
TxId     -- Nat
Result   -- State × Out    (в кейсах используются R.1 : State и R.2 : Out)
Program (Q : Type) -- TxId → Body

-- оракул внешних эффектов
E : Q → TxId → Int   -- в харнессе: fun q t => ((q * 7 + t : Nat) : Int) - 3

-- эталонная последовательная семантика
runSeq : (Q → TxId → Int) → Program Q → State → Out → Journal → Result
```

Конструкторы (используются в кейсах как анонимные `.ctor`, значит это индуктивные типы):

```lean
inductive Expr
  | const (n : Int)
  | var   (x : String)
  | add   (a b : Expr)
  | mul   (a b : Expr)

inductive Body
  | done
  | read  (c x : String) (k : Body)
  | write (c : String) (e : Expr) (k : Body)
  | emit  (e : Expr) (k : Body)
  | ite   (e : Expr) (b₁ b₂ : Body)
  | ext   (q : Q) (x : String) (k : Body)
```

## 2. Семантика (достоверно — зеркалируется витнессом)

- `runBody E t : State → Env → Out → Body → State × Out`. `read` берёт значение из состояния,
  `write` пишет в состояние, `emit` дописывает в хвост `Out`, `ite` идёт в ветку `b₂` при
  значении `0` и в `b₁` иначе, `ext q x k` связывает `x` с `E q t`.
- `runSeq` — фолд журнала: для каждого `t ∈ J` запускается `runBody` с **свежим** окружением
  `ρ₀ = fun _ => 0`.
- Инструментированная семантика `runInstr` — та же, но с write-set `w`, read-set `rs` и
  снапшотом `σ`: `read c` при `c ∈ w` возвращает собственную запись (read-your-own-writes),
  иначе читает `σ c` и **дописывает пару `(c, σ c)` в read-set**.
- `runTx t σ b = runInstr` из пустых `w`, `ρ₀`, `o`, `rs`.
- `validates S rs = ∀ (c, v) ∈ rs, S c = v`.
- Применение write-set: `applyW S w`, поячеечная перезапись.

## 3. Интерфейс L4 (единственный фрагмент Lean, сохранившийся дословно)

```lean
structure SoundSubstrate (Q) (E) (P) where
  Sched   : Type
  Run     : State → Out → Journal → Sched → State → Out → Prop
  proj    : Sched → List TxId
  forced  : Run s o J sc s' o' → proj sc = J
  refines : Run s o J sc s' o' → EvalSeq E P s o (proj sc) s' o'
```

Ключевое свойство, проверенное рецензентом перед заморозкой v5: интерфейс **нецикличен** —
`refines` говорит о `proj sc`, а не о `J`, и формулируется через индуктивное отношение
`EvalSeq`, а не через равенство с функцией `runSeq`. Ни одно поле не упоминает
`execute (P, J) = Seq (P, J)`; это равенство — производная теорема.

## 4. Что нужно передоказать, по слоям

Имена ниже взяты из State of Project v5.1 дословно; тел доказательств нет.

**L1 — детерминированный фолд.** `runSeq` тотален и детерминирован; `runSeq_sound` связывает
функцию `runSeq` с отношением `EvalSeq`; `seq_deterministic` — детерминизм отношения.

**L2 — ordered commit.** При фиксации строго в порядке журнала и успешной валидации снапшота
результат параллельного прогона равен `Seq(P, J)` при **любых** снапшотах. Это несущая лемма
для `trace_refines_seq`.

**L3A / L3B — граница расширений.** L3A: какие расширения наблюдаемого сохраняют свойство X.
L3B: контрпример `scheduleCounter` — наблюдаемое, зависящее от расписания, ломает X.

**L3.5 — три уровня совпадения.** Строгие включения: semantic ⊊ observable ⊊ coincidence.
Валидационный исход не закодирован в семантической проекции: он относится к admissibility, а
не к `proj`. Остальное — implementation artifacts.

**L4 — независимость от субстрата.** Файл `Lemma4.lean`, перечень объектов:

| Имя | Роль |
| --- | --- |
| `SoundSubstrate` | интерфейс (§3) |
| `optimisticSubstrate` | экземпляр: `RunTrace` с динамической валидацией |
| `wavefrontSubstrate` | экземпляр: `WaveRun` со статическим `WaveOk`, без валидации |
| `substrate_run_eq_seq` | `refines + forced + seq_deterministic + runSeq_sound` |
| `substrate_independence` | `executeA = Seq ∧ executeB = Seq ⇒ executeA = executeB` |
| `trace_refines_seq` | содержательное доказательство для оптимистической машины (через L2) |
| `wave_refines_seq_aux` | frame-теорема для волнового субстрата |
| `wave_progress`, `trace_progress` | прогресс обеих машин |
| `wave_partition_artifact` | разбиение на волны — implementation artifact |
| `cross_substrate_witness` | кросс-субстратный свидетель через `≈_J` |
| `SubstrateComplete` | непустота класса: ∃ легальный прогон (не liveness) |
| `optimistic_complete`, `wavefront_complete` | экземпляры полноты |
| `implements_M0_execute_eq` | sound + complete = `ImplementsM₀` |

Определения волнового субстрата (зеркало в витнессе): футпринт `cellsOf` тела транзакции,
`DisjCells` — непересечение футпринтов, `WaveOk P ts` — попарная непересекаемость внутри
волны, `WaveRun` — последовательное применение волн.

## 5. Порядок восстановления

Снизу вверх, каждый слой сверяется с витнессом:

1. §1–§2 этого файла → компилируемый `Lemma1.lean`; сразу включить Phase A витнесса
   (`python witness/m0.py a`) — она сверяет `runSeq` в Lean с эталонным интерпретатором на
   случайных программах и ловит расхождения транскрипции.
2. L2 поверх инструментированной семантики; Phase B становится осмысленной.
3. L3A/L3B/L3.5.
4. L4 — интерфейс из §3 и два экземпляра.

Пока Phase A не работает (нет `Lemma4.lean`), витнесс сверяет два субстрата между собой и с
собственным эталоном, но не с Lean. Это ослабленный, но не бесполезный режим.
