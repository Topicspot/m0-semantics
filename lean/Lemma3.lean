/-
  M₀ mechanization — Lemma 3 (Boundary theorem), in the agreed split:

  * Lemma 3A — EXTENSION PRESERVATION (the schema).
    The language is parameterized by a primitive effect
        ext q x  ≡  x := E(q, logical_time)
    for an ARBITRARY query type Q and oracle E : Q → TxId → Int.
    By its very type, E observes only (query, logical time / journal
    position) — never the schedule.  Theorem 3A: for EVERY such
    extension, the whole Lemma-2 development goes through:
    Parallel_E(P,J) = Seq_E(P,J).  This is the boundary from the
    allowed side:  o = f(state, journal, logical_time) preserves X.
    Corollaries: `event`-through-journal and `newcell(id := h(journal
    position))` are safe — allocation as such does NOT break X.

  * Lemma 3B — BOUNDARY COUNTEREXAMPLE (mechanized).
    A machine whose primitive observes the EXECUTION RELATION: the
    oracle value is the machine's attempt counter (advanced by every
    attempt, committed or aborted).  Two legal runs of the same
    (P, J) from the same state produce different Observables.
    o = f(schedule) breaks X.  The forbidden observable is exactly
    the execution order, not any particular feature like allocation.

  * Necessity lemmas (2/3 of the minimality triangle, and the
    separation of OrderCorrectness from ValidationCorrectness):
      - `order_necessary`: validation alone, without ordered commit,
        admits a non-deterministic outcome;
      - `validation_necessary`: ordered commit alone, without
        validation, admits a lost update (result ≠ Seq).
    The third side (granularity → parallelism) remains EXPERIMENTALLY
    SUPPORTED ONLY (J1) and is deliberately not claimed here.

  * Observable is an explicit projection of Result; the boundary is
    stated in terms of Observable, not internal states.

  Terminology note (per review): purity of bodies is DERIVED FROM THE
  SEMANTIC CLOSURE OF THE OBJECT LANGUAGE — expressions read locals
  only, all external observation is factored through `read` (cells)
  and `ext` (journal/logical time).  That factorization IS the
  definition of the closed semantic universe; `clock()`, `random()`,
  `network()` cannot be "added later" without changing the language —
  which is exactly what 3B demonstrates.

  Self-contained: `lean Lemma3.lean`.  The §0–§3 development mirrors
  Lemma2.lean with the `ext` primitive threaded through every
  definition and proof; Lemma 2 is the special case Q = Empty.
-/

/- ================================================================
   §0  The extended M₀ body language and sequential semantics
   ================================================================ -/

abbrev Cell : Type := String
abbrev Var  : Type := String
abbrev State : Type := Cell → Int
abbrev Env   : Type := Var → Int
abbrev Out   : Type := List Int
abbrev TxId := Nat
abbrev Journal := List TxId

/-- Expressions read LOCALS ONLY (semantic closure: all external
    observation is factored through `read` and `ext`). -/
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

/-- Bodies, extended with the primitive effect `ext q x k`:
    x := E(q, logical_time); continue with k. -/
inductive Body (Q : Type) where
  | done  : Body Q
  | read  : Cell → Var → Body Q → Body Q
  | write : Cell → Expr → Body Q → Body Q
  | emit  : Expr → Body Q → Body Q
  | ite   : Expr → Body Q → Body Q → Body Q
  | ext   : Q → Var → Body Q → Body Q

def updEnv (ρ : Env) (x : Var) (n : Int) : Env :=
  fun y => if y = x then n else ρ y

def updState (s : State) (c : Cell) (n : Int) : State :=
  fun d => if d = c then n else s d

/-- Reference big-step evaluation, at logical time t, under oracle E. -/
inductive EvalBody {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    State → Env → Out → Body Q → State → Out → Prop where
  | done : EvalBody E t s ρ o .done s o
  | read :
      EvalBody E t s (updEnv ρ x (s c)) o k s' o' →
      EvalBody E t s ρ o (.read c x k) s' o'
  | write :
      EvalBody E t (updState s c (evalExpr ρ e)) ρ o k s' o' →
      EvalBody E t s ρ o (.write c e k) s' o'
  | emit :
      EvalBody E t s ρ (o ++ [evalExpr ρ e]) k s' o' →
      EvalBody E t s ρ o (.emit e k) s' o'
  | iteTrue :
      evalExpr ρ e ≠ 0 →
      EvalBody E t s ρ o b₁ s' o' →
      EvalBody E t s ρ o (.ite e b₁ b₂) s' o'
  | iteFalse :
      evalExpr ρ e = 0 →
      EvalBody E t s ρ o b₂ s' o' →
      EvalBody E t s ρ o (.ite e b₁ b₂) s' o'
  | ext :
      EvalBody E t s (updEnv ρ x (E q t)) o k s' o' →
      EvalBody E t s ρ o (.ext q x k) s' o'

abbrev Program (Q : Type) := TxId → Body Q

def ρ₀ : Env := fun _ => 0

/-- Sequential fold of the journal (reference semantics). -/
inductive EvalSeq {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → State → Out → Prop where
  | nil  : EvalSeq E P s o [] s o
  | cons :
      EvalBody E t s ρ₀ o (P t) s' o' →
      EvalSeq E P s' o' J s'' o'' →
      EvalSeq E P s o (t :: J) s'' o''

/-- Result and its observable projection: the boundary of X is stated
    about Observable, not about internal machine states. -/
abbrev Result := State × Out
def Observable (r : Result) : Out := r.2

theorem evalBody_det {Q : Type} {E : Q → TxId → Int} {t : TxId}
    {s : State} {ρ : Env} {o : Out} {b : Body Q}
    (h₁ : EvalBody E t s ρ o b s₁ o₁) (h₂ : EvalBody E t s ρ o b s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  induction h₁ generalizing s₂ o₂ with
  | done => cases h₂ with | done => exact ⟨rfl, rfl⟩
  | read _ ih  => cases h₂ with | read h  => exact ih h
  | write _ ih => cases h₂ with | write h => exact ih h
  | emit _ ih  => cases h₂ with | emit h  => exact ih h
  | iteTrue hc _ ih =>
      cases h₂ with
      | iteTrue _ h    => exact ih h
      | iteFalse hc' _ => exact absurd hc' hc
  | iteFalse hc _ ih =>
      cases h₂ with
      | iteTrue hc' _ => exact absurd hc hc'
      | iteFalse _ h  => exact ih h
  | ext _ ih => cases h₂ with | ext h => exact ih h

/-- Lemma 1 for the extended language: Seq_E is deterministic. -/
theorem seq_deterministic {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h₁ : EvalSeq E P s o J s₁ o₁) (h₂ : EvalSeq E P s o J s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  induction h₁ generalizing s₂ o₂ with
  | nil => cases h₂ with | nil => exact ⟨rfl, rfl⟩
  | cons hb _ ih =>
      cases h₂ with
      | cons hb' hrest =>
          obtain ⟨hs, ho⟩ := evalBody_det hb hb'
          subst hs; subst ho
          exact ih hrest

def runBody {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    State → Env → Out → Body Q → State × Out
  | s, _, o, .done => (s, o)
  | s, ρ, o, .read c x k  => runBody E t s (updEnv ρ x (s c)) o k
  | s, ρ, o, .write c e k => runBody E t (updState s c (evalExpr ρ e)) ρ o k
  | s, ρ, o, .emit e k    => runBody E t s ρ (o ++ [evalExpr ρ e]) k
  | s, ρ, o, .ite e b₁ b₂ =>
      if evalExpr ρ e = 0 then runBody E t s ρ o b₂ else runBody E t s ρ o b₁
  | s, ρ, o, .ext q x k   => runBody E t s (updEnv ρ x (E q t)) o k

def runSeq {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → State × Out
  | s, o, [] => (s, o)
  | s, o, t :: J =>
      let r := runBody E t s ρ₀ o (P t)
      runSeq E P r.1 r.2 J

theorem runBody_sound {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b s ρ o, EvalBody E t s ρ o b (runBody E t s ρ o b).1 (runBody E t s ρ o b).2 := by
  intro b
  induction b with
  | done => intro s ρ o; exact .done
  | read c x k ih  => intro s ρ o; exact .read (ih ..)
  | write c e k ih => intro s ρ o; exact .write (ih ..)
  | emit e k ih    => intro s ρ o; exact .emit (ih ..)
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro s ρ o
      by_cases hc : evalExpr ρ e = 0
      · simpa [runBody, hc] using .iteFalse hc (ih₂ s ρ o)
      · simpa [runBody, hc] using .iteTrue hc (ih₁ s ρ o)
  | ext q x k ih   => intro s ρ o; exact .ext (ih ..)

theorem runSeq_sound {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ J s o, EvalSeq E P s o J (runSeq E P s o J).1 (runSeq E P s o J).2 := by
  intro J
  induction J with
  | nil => intro s o; exact .nil
  | cons t J ih =>
      intro s o
      exact .cons (runBody_sound ..) (ih ..)

/- ================================================================
   §1  Instrumented semantics with read-set (extension threaded)
   ================================================================ -/

abbrev Writes : Type := Cell → Option Int
abbrev ReadSet : Type := List (Cell × Int)

def updW (w : Writes) (c : Cell) (n : Int) : Writes :=
  fun d => if d = c then some n else w d

def applyW (S : State) (w : Writes) : State :=
  fun c => (w c).getD (S c)

def w₀ : Writes := fun _ => none

/-- Instrumented evaluation against snapshot σ, at logical time t.
    `ext` consults only (q, t): no snapshot observation, hence no
    read-set entry — by TYPE it cannot depend on the schedule. -/
def runInstr {Q : Type} (E : Q → TxId → Int) (t : TxId) (σ : State) :
    Writes → Env → Out → ReadSet → Body Q → Writes × Out × ReadSet
  | w, _, o, rs, .done => (w, o, rs)
  | w, ρ, o, rs, .read c x k =>
      match w c with
      | some v => runInstr E t σ w (updEnv ρ x v) o rs k
      | none   => runInstr E t σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k
  | w, ρ, o, rs, .write c e k => runInstr E t σ (updW w c (evalExpr ρ e)) ρ o rs k
  | w, ρ, o, rs, .emit e k    => runInstr E t σ w ρ (o ++ [evalExpr ρ e]) rs k
  | w, ρ, o, rs, .ite e b₁ b₂ =>
      if evalExpr ρ e = 0 then runInstr E t σ w ρ o rs b₂ else runInstr E t σ w ρ o rs b₁
  | w, ρ, o, rs, .ext q x k   => runInstr E t σ w (updEnv ρ x (E q t)) o rs k

def runTx {Q : Type} (E : Q → TxId → Int) (t : TxId) (σ : State) (b : Body Q) :
    Writes × Out × ReadSet :=
  runInstr E t σ w₀ ρ₀ [] [] b

def validates (S : State) (rs : ReadSet) : Prop := ∀ p ∈ rs, S p.1 = p.2

theorem runInstr_rs_mono {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b σ w ρ o rs p, p ∈ rs → p ∈ (runInstr E t σ w ρ o rs b).2.2 := by
  intro b
  induction b with
  | done => intro σ w ρ o rs p hp; simpa [runInstr] using hp
  | read c x k ih =>
      intro σ w ρ o rs p hp
      cases hw : w c with
      | some v => simpa [runInstr, hw] using ih σ w (updEnv ρ x v) o rs p hp
      | none   =>
          simp only [runInstr, hw]
          exact ih σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) p
            (List.mem_append_left _ hp)
  | write c e k ih =>
      intro σ w ρ o rs p hp
      simpa [runInstr] using ih σ (updW w c (evalExpr ρ e)) ρ o rs p hp
  | emit e k ih =>
      intro σ w ρ o rs p hp
      simpa [runInstr] using ih σ w ρ (o ++ [evalExpr ρ e]) rs p hp
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro σ w ρ o rs p hp
      by_cases hc : evalExpr ρ e = 0
      · simpa [runInstr, hc] using ih₂ σ w ρ o rs p hp
      · simpa [runInstr, hc] using ih₁ σ w ρ o rs p hp
  | ext q x k ih =>
      intro σ w ρ o rs p hp
      simpa [runInstr] using ih σ w (updEnv ρ x (E q t)) o rs p hp

theorem runInstr_rs_from_snapshot {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b σ w ρ o rs p, p ∈ (runInstr E t σ w ρ o rs b).2.2 → p ∈ rs ∨ σ p.1 = p.2 := by
  intro b
  induction b with
  | done => intro σ w ρ o rs p hp; exact .inl (by simpa [runInstr] using hp)
  | read c x k ih =>
      intro σ w ρ o rs p hp
      cases hw : w c with
      | some v => exact ih σ w (updEnv ρ x v) o rs p (by simpa [runInstr, hw] using hp)
      | none   =>
          have hp' : p ∈ (runInstr E t σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k).2.2 := by
            simpa [runInstr, hw] using hp
          rcases ih σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) p hp' with h | h
          · rcases List.mem_append.mp h with h | h
            · exact .inl h
            · right
              have : p = (c, σ c) := by simpa using h
              subst this; rfl
          · exact .inr h
  | write c e k ih =>
      intro σ w ρ o rs p hp
      exact ih σ (updW w c (evalExpr ρ e)) ρ o rs p (by simpa [runInstr] using hp)
  | emit e k ih =>
      intro σ w ρ o rs p hp
      exact ih σ w ρ (o ++ [evalExpr ρ e]) rs p (by simpa [runInstr] using hp)
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro σ w ρ o rs p hp
      by_cases hc : evalExpr ρ e = 0
      · exact ih₂ σ w ρ o rs p (by simpa [runInstr, hc] using hp)
      · exact ih₁ σ w ρ o rs p (by simpa [runInstr, hc] using hp)
  | ext q x k ih =>
      intro σ w ρ o rs p hp
      exact ih σ w (updEnv ρ x (E q t)) o rs p (by simpa [runInstr] using hp)

/- ================================================================
   §2  Snapshot adequacy and realization (extension threaded)
   ================================================================ -/

/-- Snapshot adequacy for the extended language.  The `ext` case is
    the point of Lemma 3A: E(q,t) is the same under σ and S because
    it never consults the snapshot — schedule-invariance by type. -/
theorem runInstr_snapshot_adequate {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b σ S w ρ o rs,
      (∀ p ∈ (runInstr E t σ w ρ o rs b).2.2, S p.1 = p.2) →
      runInstr E t S w ρ o rs b = runInstr E t σ w ρ o rs b := by
  intro b
  induction b with
  | done => intro σ S w ρ o rs _; rfl
  | read c x k ih =>
      intro σ S w ρ o rs h
      cases hw : w c with
      | some v =>
          simp only [runInstr, hw]
          exact ih σ S w (updEnv ρ x v) o rs (by simpa [runInstr, hw] using h)
      | none   =>
          have hmem : (c, σ c) ∈ (runInstr E t σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k).2.2 :=
            runInstr_rs_mono E t k σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) (c, σ c)
              (List.mem_append_right _ (by simp))
          have hSc : S c = σ c :=
            h (c, σ c) (by simpa [runInstr, hw] using hmem)
          simp only [runInstr, hw, hSc]
          exact ih σ S w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)])
            (by simpa [runInstr, hw] using h)
  | write c e k ih =>
      intro σ S w ρ o rs h
      simp only [runInstr]
      exact ih σ S (updW w c (evalExpr ρ e)) ρ o rs (by simpa [runInstr] using h)
  | emit e k ih =>
      intro σ S w ρ o rs h
      simp only [runInstr]
      exact ih σ S w ρ (o ++ [evalExpr ρ e]) rs (by simpa [runInstr] using h)
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro σ S w ρ o rs h
      by_cases hc : evalExpr ρ e = 0
      · simp only [runInstr, hc, if_pos]
        exact ih₂ σ S w ρ o rs (by simpa [runInstr, hc] using h)
      · simp only [runInstr, hc, if_false]
        exact ih₁ σ S w ρ o rs (by simpa [runInstr, hc] using h)
  | ext q x k ih =>
      intro σ S w ρ o rs h
      simp only [runInstr]
      exact ih σ S w (updEnv ρ x (E q t)) o rs (by simpa [runInstr] using h)

theorem applyW_updW (S : State) (w : Writes) (c : Cell) (n : Int) :
    applyW S (updW w c n) = updState (applyW S w) c n := by
  funext d
  by_cases hd : d = c <;> simp [applyW, updW, updState, hd]

theorem applyW_empty (S : State) : applyW S w₀ = S := by
  funext c; simp [applyW, w₀]

theorem runInstr_realizes_runBody {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b S w ρ o rs,
      runBody E t (applyW S w) ρ o b
        = (applyW S (runInstr E t S w ρ o rs b).1, (runInstr E t S w ρ o rs b).2.1) := by
  intro b
  induction b with
  | done => intro S w ρ o rs; simp [runBody, runInstr]
  | read c x k ih =>
      intro S w ρ o rs
      cases hw : w c with
      | some v =>
          have hval : applyW S w c = v := by simp [applyW, hw]
          simp only [runBody, runInstr, hw, hval]
          exact ih S w (updEnv ρ x v) o rs
      | none   =>
          have hval : applyW S w c = S c := by simp [applyW, hw]
          simp only [runBody, runInstr, hw, hval]
          exact ih S w (updEnv ρ x (S c)) o (rs ++ [(c, S c)])
  | write c e k ih =>
      intro S w ρ o rs
      simp only [runBody, runInstr, ← applyW_updW]
      exact ih S (updW w c (evalExpr ρ e)) ρ o rs
  | emit e k ih =>
      intro S w ρ o rs
      simp only [runBody, runInstr]
      exact ih S w ρ (o ++ [evalExpr ρ e]) rs
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro S w ρ o rs
      by_cases hc : evalExpr ρ e = 0
      · simp only [runBody, runInstr, hc, if_pos]
        exact ih₂ S w ρ o rs
      · simp only [runBody, runInstr, hc, if_false]
        exact ih₁ S w ρ o rs
  | ext q x k ih =>
      intro S w ρ o rs
      simp only [runBody, runInstr]
      exact ih S w (updEnv ρ x (E q t)) o rs

theorem runBody_out_shift {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b s ρ o, runBody E t s ρ o b = ((runBody E t s ρ [] b).1, o ++ (runBody E t s ρ [] b).2) := by
  intro b
  induction b with
  | done => intro s ρ o; simp [runBody]
  | read c x k ih  => intro s ρ o; simp only [runBody]; exact ih s (updEnv ρ x (s c)) o
  | write c e k ih => intro s ρ o; simp only [runBody]; exact ih (updState s c (evalExpr ρ e)) ρ o
  | emit e k ih    =>
      intro s ρ o
      simp only [runBody, List.nil_append]
      rw [ih s ρ (o ++ [evalExpr ρ e]), ih s ρ [evalExpr ρ e]]
      simp
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro s ρ o
      by_cases hc : evalExpr ρ e = 0
      · simp only [runBody, hc, if_pos]; exact ih₂ s ρ o
      · simp only [runBody, hc, if_false]; exact ih₁ s ρ o
  | ext q x k ih   => intro s ρ o; simp only [runBody]; exact ih s (updEnv ρ x (E q t)) o

theorem commit_step {Q : Type} (E : Q → TxId → Int) (t : TxId)
    (S : State) (b : Body Q) (o : Out) (σ : State)
    (hval : validates S (runTx E t σ b).2.2) :
    runBody E t S ρ₀ o b = (applyW S (runTx E t σ b).1, o ++ (runTx E t σ b).2.1) := by
  have hadq : runInstr E t S w₀ ρ₀ [] [] b = runInstr E t σ w₀ ρ₀ [] [] b :=
    runInstr_snapshot_adequate E t b σ S w₀ ρ₀ [] [] (fun p hp => hval p hp)
  have hreal := runInstr_realizes_runBody E t b S w₀ ρ₀ [] []
  rw [applyW_empty] at hreal
  have hrefS : runBody E t S ρ₀ [] b = (applyW S (runTx E t σ b).1, (runTx E t σ b).2.1) := by
    unfold runTx
    rw [← hadq]
    exact hreal
  rw [runBody_out_shift E t b S ρ₀ o, hrefS]

theorem commit_evalBody {Q : Type} (E : Q → TxId → Int) (t : TxId)
    (S : State) (b : Body Q) (o : Out) (σ : State)
    (hval : validates S (runTx E t σ b).2.2) :
    EvalBody E t S ρ₀ o b (applyW S (runTx E t σ b).1) (o ++ (runTx E t σ b).2.1) := by
  have hb := runBody_sound E t b S ρ₀ o
  rw [commit_step E t S b o σ hval] at hb
  exact hb

/- ================================================================
   §3  Lemma 3A — extension preservation theorem
   ================================================================ -/

/-- The parallel machine for the EXTENDED language: journal-ordered
    commit, adversary-chosen arbitrary snapshots, read-set validation.
    OrderCorrectness lives in the index discipline (only the head of
    the remaining journal commits); ValidationCorrectness is the
    explicit `validates` premise — the two conditions are separated
    below by the necessity lemmas, each with its own counterexample
    machine (§5). -/
inductive Par {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → State → Out → Prop where
  | nil : Par E P s o [] s o
  | commit (σ : State) :
      validates s (runTx E t σ (P t)).2.2 →
      Par E P (applyW s (runTx E t σ (P t)).1) (o ++ (runTx E t σ (P t)).2.1) J s' o' →
      Par E P s o (t :: J) s' o'

theorem par_refines_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : Par E P s o J s' o') : EvalSeq E P s o J s' o' := by
  induction h with
  | nil => exact .nil
  | commit σ hval _ ih => exact .cons (commit_evalBody _ _ _ _ _ σ hval) ih

theorem par_progress {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ J s o, Par E P s o J (runSeq E P s o J).1 (runSeq E P s o J).2 := by
  intro J
  induction J with
  | nil => intro s o; exact Par.nil
  | cons t J ih =>
      intro s o
      have hval : validates s (runTx E t s (P t)).2.2 := by
        intro p hp
        rcases runInstr_rs_from_snapshot E t (P t) s w₀ ρ₀ [] [] p hp with h | h
        · cases h
        · exact h
      refine Par.commit s hval ?_
      have hstep := commit_step E t s (P t) o s hval
      have hfold : runSeq E P s o (t :: J)
          = runSeq E P (applyW s (runTx E t s (P t)).1) (o ++ (runTx E t s (P t)).2.1) J := by
        simp only [runSeq, hstep]
      rw [hfold]
      exact ih (applyW s (runTx E t s (P t)).1) (o ++ (runTx E t s (P t)).2.1)

/-- **Lemma 3A (Extension preservation).**  For EVERY query type Q and
    EVERY oracle E : Q → TxId → Int — i.e. every primitive effect
    whose value is a function of (query, logical time / journal
    position) and therefore schedule-invariant by construction — the
    extended semantics preserves X: a completed parallel execution
    exists, and every parallel execution yields the unique Seq_E
    result (in particular the same Observable). -/
theorem lemma3A_extension_preservation
    {Q : Type} (E : Q → TxId → Int) (P : Program Q) (J : Journal) (s : State) :
    Par E P s [] J (runSeq E P s [] J).1 (runSeq E P s [] J).2 ∧
    ∀ s' o', Par E P s [] J s' o' → (s', o') = runSeq E P s [] J := by
  refine ⟨par_progress E P J s [], ?_⟩
  intro s' o' h
  obtain ⟨hs, ho⟩ :=
    seq_deterministic (par_refines_seq h) (runSeq_sound E P J s [])
  exact Prod.ext hs ho

/-- Corollary: Lemma 2 is the degenerate instance Q = Empty
    (no extension at all). -/
theorem lemma2_commit_order (P : Program Empty) (J : Journal) (s : State) :
    Par (fun q _ => nomatch q) P s [] J
      (runSeq (fun q _ => nomatch q) P s [] J).1
      (runSeq (fun q _ => nomatch q) P s [] J).2 ∧
    ∀ s' o', Par (fun q _ => nomatch q) P s [] J s' o' →
      (s', o') = runSeq (fun q _ => nomatch q) P s [] J :=
  lemma3A_extension_preservation _ P J s

/-- Corollary: ALLOCATION AS SUCH DOES NOT BREAK X.  An allocator
    whose fresh identifiers are a function of the journal position —
    `newcell(id := h(logical_time))` — is a schedule-invariant
    extension and preserves X.  (Same shape covers `event`/`request`
    payloads drawn from the journal.)  The breakage in 3B comes from
    observing the execution relation, not from allocating. -/
theorem safe_alloc_by_journal_position
    (h : TxId → Int) (P : Program Unit) (J : Journal) (s : State) :
    Par (fun _ t => h t) P s [] J
      (runSeq (fun _ t => h t) P s [] J).1
      (runSeq (fun _ t => h t) P s [] J).2 ∧
    ∀ s' o', Par (fun _ t => h t) P s [] J s' o' →
      (s', o') = runSeq (fun _ t => h t) P s [] J :=
  lemma3A_extension_preservation _ P J s

/- ================================================================
   §4  Lemma 3B — the boundary counterexample (mechanized)
   ================================================================ -/

/-- A machine whose primitive observes the EXECUTION RELATION: the
    configuration carries an attempt counter n, advanced by every
    attempt — aborted (`abort`: an attempt ran and was discarded) or
    committed.  The `ext` oracle of the attempt returns the current
    counter: `scheduleCounter`.  Ordered commit and validation are
    still enforced — the machine is otherwise perfectly disciplined. -/
inductive ParSched (P : Program Unit) :
    Nat → State → Out → Journal → Nat → State → Out → Prop where
  | nil : ParSched P n s o [] n s o
  | abort {n n' : Nat} :
      ParSched P (n + 1) s o (t :: J) n' s' o' →
      ParSched P n s o (t :: J) n' s' o'
  | commit {n n' : Nat} (σ : State) :
      validates s (runTx (fun _ _ => (n : Int)) t σ (P t)).2.2 →
      ParSched P (n + 1)
        (applyW s (runTx (fun _ _ => (n : Int)) t σ (P t)).1)
        (o ++ (runTx (fun _ _ => (n : Int)) t σ (P t)).2.1) J n' s' o' →
      ParSched P n s o (t :: J) n' s' o'

/-- The witness program: x := scheduleCounter; emit x. -/
def Pctr : Program Unit := fun _ => .ext () "x" (.emit (.var "x") .done)

def s₀ : State := fun _ => 0

/-- **Lemma 3B (Boundary counterexample).**  With `scheduleCounter`,
    two legal machine runs of the SAME program, journal, and initial
    state — differing only in the schedule (one clean commit vs one
    abort then commit) — produce different Observables.  X is broken:
    ∃ e₁ e₂ : schedule(e₁) ≠ schedule(e₂) ∧ Observable(e₁) ≠ Observable(e₂).
    Together with 3A this pins the boundary: allowed
    o = f(state, journal, logical_time); forbidden o = f(schedule). -/
theorem lemma3B_boundary_counterexample :
    ∃ (r₁ r₂ : Result),
      (∃ n, ParSched Pctr 0 s₀ [] [0] n r₁.1 r₁.2) ∧
      (∃ n, ParSched Pctr 0 s₀ [] [0] n r₂.1 r₂.2) ∧
      Observable r₁ ≠ Observable r₂ := by
  have hrun : ∀ n : Nat, runTx (fun _ _ => (n : Int)) 0 s₀ (Pctr 0)
      = (w₀, [(n : Int)], []) := by
    intro n
    simp [Pctr, runTx, runInstr, evalExpr, updEnv]
  refine ⟨(applyW s₀ w₀, [(0 : Int)]), (applyW s₀ w₀, [(1 : Int)]), ⟨1, ?_⟩, ⟨2, ?_⟩, ?_⟩
  · -- schedule A: immediate commit; the attempt sees counter 0
    refine ParSched.commit s₀ ?_ ?_
    · rw [hrun 0]; intro p hp; cases hp
    · rw [hrun 0]; exact ParSched.nil
  · -- schedule B: one abort, then commit; the attempt sees counter 1
    refine ParSched.abort (ParSched.commit s₀ ?_ ?_)
    · rw [hrun 1]; intro p hp; cases hp
    · rw [hrun 1]; exact ParSched.nil
  · simp [Observable]

/- ================================================================
   §5  Necessity lemmas: 2/3 of the minimality triangle,
       and the separation of Order- vs Validation-correctness
   ================================================================ -/

/-- Machine WITHOUT ordered commit: validation intact, but any pending
    journal element may commit.  (No extension: E is trivial.) -/
inductive ParUnordered (P : Program Unit) :
    State → Out → List TxId → State → Out → Prop where
  | nil : ParUnordered P s o [] s o
  | commit (σ : State) (t : TxId) (hmem : t ∈ pend) :
      validates s (runTx (fun _ _ => 0) t σ (P t)).2.2 →
      ParUnordered P (applyW s (runTx (fun _ _ => 0) t σ (P t)).1)
        (o ++ (runTx (fun _ _ => 0) t σ (P t)).2.1) (pend.erase t) s' o' →
      ParUnordered P s o pend s' o'

/-- tx 0 writes c := 1; tx 1 writes c := 2. -/
def Pord : Program Unit := fun t =>
  if t = 0 then .write "c" (.const 1) .done else .write "c" (.const 2) .done

/-- **Order is necessary.**  With validation but without ordered
    commit, the same (P, journal, state) admits two completed runs
    with different final contents of cell "c": non-deterministic
    outcome, X broken.  (First impossibility side of the triangle;
    also: ValidationCorrectness alone ≠ correctness.) -/
theorem order_necessary :
    ∃ (s₁ : State) (o₁ : Out) (s₂ : State) (o₂ : Out),
      ParUnordered Pord s₀ [] [0, 1] s₁ o₁ ∧
      ParUnordered Pord s₀ [] [0, 1] s₂ o₂ ∧
      s₁ "c" ≠ s₂ "c" := by
  have h0 : runTx (fun _ _ => (0 : Int)) 0 s₀ (Pord 0) = (updW w₀ "c" 1, [], []) := by
    simp [Pord, runTx, runInstr, evalExpr]
  have h1 : ∀ σ : State, runTx (fun _ _ => (0 : Int)) 1 σ (Pord 1) = (updW w₀ "c" 2, [], []) := by
    intro σ; simp [Pord, runTx, runInstr, evalExpr]
  refine ⟨applyW (applyW s₀ (updW w₀ "c" 1)) (updW w₀ "c" 2), [],
          applyW (applyW s₀ (updW w₀ "c" 2)) (updW w₀ "c" 1), [], ?_, ?_, ?_⟩
  · -- commit order 0, then 1 (journal order): c ends at 2
    refine ParUnordered.commit s₀ 0 (by simp) ?_ ?_
    · rw [h0]; intro p hp; cases hp
    · rw [h0]
      refine ParUnordered.commit s₀ 1 (by simp) ?_ ?_
      · rw [h1]; intro p hp; cases hp
      · rw [h1]; simpa using ParUnordered.nil
  · -- commit order 1, then 0 (violating journal order): c ends at 1
    refine ParUnordered.commit s₀ 1 (by simp) ?_ ?_
    · rw [h1]; intro p hp; cases hp
    · rw [h1]
      refine ParUnordered.commit s₀ 0 (by simp) ?_ ?_
      · rw [h0]; intro p hp; cases hp
      · rw [h0]; simpa using ParUnordered.nil
  · simp [applyW, updW]

/-- Machine WITHOUT validation: ordered commit intact, but any
    (possibly stale) snapshot commits unconditionally. -/
inductive ParUnvalidated (P : Program Unit) :
    State → Out → Journal → State → Out → Prop where
  | nil : ParUnvalidated P s o [] s o
  | commit (σ : State) :
      ParUnvalidated P (applyW s (runTx (fun _ _ => 0) t σ (P t)).1)
        (o ++ (runTx (fun _ _ => 0) t σ (P t)).2.1) J s' o' →
      ParUnvalidated P s o (t :: J) s' o'

/-- Both transactions increment cell "c": read c x; write c (x+1). -/
def Pinc : Program Unit := fun _ =>
  .read "c" "x" (.write "c" (.add (.var "x") (.const 1)) .done)

/-- **Validation is necessary.**  With ordered commit but without
    validation, a stale snapshot produces the classic lost update:
    the machine completes with c = 1 while Seq gives c = 2.
    (Second impossibility side; also: OrderCorrectness alone ≠
    correctness.) -/
theorem validation_necessary :
    ∃ (s' : State) (o' : Out),
      ParUnvalidated Pinc s₀ [] [0, 1] s' o' ∧
      s' "c" ≠ (runSeq (fun _ _ => (0 : Int)) Pinc s₀ [] [0, 1]).1 "c" := by
  have hrun : ∀ (t : TxId) (σ : State),
      runTx (fun _ _ => (0 : Int)) t σ (Pinc t)
        = (updW w₀ "c" (σ "c" + 1), [], [("c", σ "c")]) := by
    intro t σ
    simp [Pinc, runTx, runInstr, evalExpr, updEnv, w₀]
  refine ⟨applyW (applyW s₀ (updW w₀ "c" (s₀ "c" + 1))) (updW w₀ "c" (s₀ "c" + 1)), [], ?_, ?_⟩
  · -- tx 0 commits from fresh s₀; tx 1 commits from STALE snapshot s₀
    refine ParUnvalidated.commit s₀ ?_
    rw [hrun 0 s₀]
    refine ParUnvalidated.commit s₀ ?_
    rw [hrun 1 s₀]
    simpa using ParUnvalidated.nil
  · -- machine: c = 1;  Seq: c = 2
    have hpar : applyW (applyW s₀ (updW w₀ "c" (s₀ "c" + 1))) (updW w₀ "c" (s₀ "c" + 1)) "c"
        = 1 := by
      simp [applyW, updW, s₀]
    have hseq : (runSeq (fun _ _ => (0 : Int)) Pinc s₀ [] [0, 1]).1 "c" = 2 := by
      simp [Pinc, runSeq, runBody, evalExpr, updEnv, updState, s₀]
    rw [hpar, hseq]
    decide
