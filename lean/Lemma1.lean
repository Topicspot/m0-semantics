/-
  M₀ mechanization — Lemma 1 (Deterministic fold).

  Statement: the reference (sequential) semantics
      Seq(P, J) : (State, Out)
  given as an *evaluation relation* over the closed term set of M₀,
  relates every (P, J, initial state) to at most one result.

  Design notes (faithful to m0.py / attack docs):
  * closed AST: Expr / Op / Body — no host escapes are constructible;
  * `execute(program, journal) = result`: the journal is an explicit
    input; the relation takes P and J as arguments;
  * read-your-writes inside a body (as in Ctx.read);
  * `emit` is the only output channel; Out is part of Observable;
  * proved: (1) determinism of the relation (Lemma 1 proper),
    (2) adequacy: the executable fold realizes the relation, hence
    a result always exists — Seq(P,J) has *exactly one* result.
-/

abbrev Cell : Type := String
abbrev Var  : Type := String
abbrev State : Type := Cell → Int
abbrev Env   : Type := Var → Int
abbrev Out   : Type := List Int

/-- Closed expression language (locals + constants + arithmetic). -/
inductive Expr where
  | const : Int → Expr
  | var   : Var → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr

def evalExpr (ρ : Env) : Expr → Int
  | .const n => n
  | .var v   => ρ v
  | .add a b => evalExpr ρ a + evalExpr ρ b
  | .mul a b => evalExpr ρ a * evalExpr ρ b

/-- Closed operation set of a transaction body. -/
inductive Op where
  | read  : Cell → Var → Op    -- x := cell (read-your-writes)
  | write : Cell → Expr → Op   -- cell := e
  | emit  : Expr → Op          -- output e

abbrev Body := List Op

def updEnv (ρ : Env) (x : Var) (n : Int) : Env :=
  fun y => if y = x then n else ρ y

def updState (s : State) (c : Cell) (n : Int) : State :=
  fun d => if d = c then n else s d

/-- Big-step evaluation of a body against a working state
    (initialized with the snapshot), threading locals and output. -/
inductive EvalBody :
    State → Env → Out → Body → State → Out → Prop where
  | done : EvalBody s ρ o [] s o
  | read :
      EvalBody s (updEnv ρ x (s c)) o rest s' o' →
      EvalBody s ρ o (.read c x :: rest) s' o'
  | write :
      EvalBody (updState s c (evalExpr ρ e)) ρ o rest s' o' →
      EvalBody s ρ o (.write c e :: rest) s' o'
  | emit :
      EvalBody s ρ (o ++ [evalExpr ρ e]) rest s' o' →
      EvalBody s ρ o (.emit e :: rest) s' o'

abbrev TxId := Nat
abbrev Program := TxId → Body
abbrev Journal := List TxId

def ρ₀ : Env := fun _ => 0

/-- Reference semantics: sequential fold of the journal.
    `execute(program, journal) = result` as a relation. -/
inductive EvalSeq :
    Program → State → Out → Journal → State → Out → Prop where
  | nil  : EvalSeq P s o [] s o
  | cons :
      EvalBody s ρ₀ o (P t) s' o' →
      EvalSeq P s' o' J s'' o'' →
      EvalSeq P s o (t :: J) s'' o''

/-- Determinism of body evaluation. -/
theorem evalBody_det
    (h₁ : EvalBody s ρ o b s₁ o₁) (h₂ : EvalBody s ρ o b s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  induction h₁ generalizing s₂ o₂ with
  | done => cases h₂ with | done => exact ⟨rfl, rfl⟩
  | read _ ih  => cases h₂ with | read h  => exact ih h
  | write _ ih => cases h₂ with | write h => exact ih h
  | emit _ ih  => cases h₂ with | emit h  => exact ih h

/-- **Lemma 1 (Deterministic fold).**
    For any program P, journal J and initial state, the sequential
    semantics relates them to at most one observable (State, Out). -/
theorem lemma1_seq_deterministic
    (h₁ : EvalSeq P s o J s₁ o₁) (h₂ : EvalSeq P s o J s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  induction h₁ generalizing s₂ o₂ with
  | nil => cases h₂ with | nil => exact ⟨rfl, rfl⟩
  | cons hb _ ih =>
      cases h₂ with
      | cons hb' hrest =>
          obtain ⟨hs, ho⟩ := evalBody_det hb hb'
          subst hs; subst ho
          exact ih hrest

/- ------------------------------------------------------------------
   Adequacy: the executable fold (the thing the Python harness runs)
   realizes the relation, so a result also *exists*.
   ------------------------------------------------------------------ -/

def runBody : State → Env → Out → Body → State × Out
  | s, _, o, [] => (s, o)
  | s, ρ, o, .read c x :: rest  => runBody s (updEnv ρ x (s c)) o rest
  | s, ρ, o, .write c e :: rest => runBody (updState s c (evalExpr ρ e)) ρ o rest
  | s, ρ, o, .emit e :: rest    => runBody s ρ (o ++ [evalExpr ρ e]) rest

def runSeq (P : Program) : State → Out → Journal → State × Out
  | s, o, [] => (s, o)
  | s, o, t :: J =>
      let r := runBody s ρ₀ o (P t)
      runSeq P r.1 r.2 J

theorem runBody_sound :
    ∀ b s ρ o, EvalBody s ρ o b (runBody s ρ o b).1 (runBody s ρ o b).2 := by
  intro b
  induction b with
  | nil => intro s ρ o; exact .done
  | cons op rest ih =>
      intro s ρ o
      cases op with
      | read c x  => exact .read (ih ..)
      | write c e => exact .write (ih ..)
      | emit e    => exact .emit (ih ..)

theorem runSeq_sound :
    ∀ J P s o, EvalSeq P s o J (runSeq P s o J).1 (runSeq P s o J).2 := by
  intro J
  induction J with
  | nil => intro P s o; exact .nil
  | cons t J ih =>
      intro P s o
      exact .cons (runBody_sound ..) (ih ..)

/-- **Corollary.** Seq(P, J) has exactly one result: it exists
    (`runSeq_sound`) and is unique (`lemma1_seq_deterministic`). -/
theorem seq_unique_result (P : Program) (J : Journal) (s : State) :
    ∃ r : State × Out, EvalSeq P s [] J r.1 r.2 ∧
      ∀ r' : State × Out, EvalSeq P s [] J r'.1 r'.2 → r' = r := by
  refine ⟨runSeq P s [] J, runSeq_sound .., ?_⟩
  intro r hr
  obtain ⟨hs, ho⟩ := lemma1_seq_deterministic hr (runSeq_sound ..)
  exact Prod.ext hs ho
