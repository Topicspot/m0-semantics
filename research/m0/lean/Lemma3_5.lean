/-
  M₀ mechanization — Lemma 3.5 (Schedule Equivalence boundary).

  Motivation (owner's review of L3): the object `≈` in the central
  claim was so far only extensional ("same Observable").  This file
  defines schedule equivalence STRUCTURALLY and separates three
  levels that were previously fused:

      semantic equivalence  (≈_J : same semantic projection)
             |  (theorem: lemma3_5_equiv_implies_observable)
             v
      observable equivalence
             |  (strict: observable_coincidence_not_equiv)
             v
      implementation coincidence

  A SCHEDULE is reified as a trace of events of the parallel machine:
      attempt t σ   — a speculative attempt (snapshot σ) that was
                      aborted / discarded;
      commit  t σ   — a validated commit of journal head t from
                      snapshot σ.
  The SEMANTIC PROJECTION of a trace is the sequence of committed
  transaction ids in commit order.  It carries:
    1. commit-order            — the list order;
    2. logical time assignment — position in the list;
    3. journal consumption     — the list itself (sem_forced: it
                                 equals the consumed journal).
  Validation outcome is NOT encoded in the projection: it is enforced
  by trace legality (the `RunTrace.commit` rule requires `validates`),
  i.e. it belongs to the admissibility relation, not to `semProj`.
  Everything else — number of aborts, speculative snapshots, worker
  allocation, launch timing — is likewise not in the projection: any
  trace component not preserved by semProj is observationally
  irrelevant for X and belongs to the implementation layer.

  Results (all for the FULL extended language of Lemma 3A, i.e. with
  an arbitrary schedule-invariant primitive `ext`):

  * `sem_forced`          — journal consumption is forced: the
                            semantic projection of any legal trace is
                            exactly the consumed journal.
  * `lemma3_5_equiv_implies_observable`
                          — S₁ ≈_J S₂ ⇒ identical Result (hence
                            identical Observable), even for runs with
                            wildly different abort structure and
                            snapshots.
  * `same_journal_all_equiv`
                          — all legal complete runs of one (P, J) are
                            pairwise ≈_J: every difference between
                            them is an implementation artifact.
  * `abort_count_artifact`— explicit witness: two legal runs of the
                            same (P, J) with DIFFERENT abort counts,
                            still ≈_J (and thus same Observable).
  * `observable_coincidence_not_equiv`
                          — the converse fails: ¬(S₁ ≈_J S₂) does NOT
                            imply different Observables.  Witness: two
                            runs with different semantic projections
                            and coinciding Observables.  Equality of
                            Observables without ≈_J is coincidence of
                            implementations, not semantic identity.

  Boundary restated (owner's refinement): forbidden is not "the
  schedule" as one representation, but ANY observation that is not a
  function of the semantic inputs.  Formally (in this discrete typed
  setting): the observable must factor through the semantic inputs;
  "observable ∉ σ(semantic inputs)" is the explanatory σ-algebra
  analogy, not a formal object of this model.
  In this typed setting: an observable must factor through
  (state, journal, logical_time); abort counts, worker ids, latency,
  cache state, warp ids are all non-measurable w.r.t. the semantic
  σ-algebra and belong to one class, of which Lemma 3B's
  scheduleCounter is the canonical representative.

  Self-contained: `lean Lemma3_5.lean`.  §0–§2 are shared verbatim
  with Lemma3.lean (extended language, instrumented semantics,
  snapshot adequacy, commit realization).
-/

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
   §3  Schedules as traces; the semantic projection
   ================================================================ -/

/-- Machine events: a schedule reified.  `attempt` is a speculative
    execution that was aborted or discarded; `commit` is a validated,
    journal-ordered commit. -/
inductive Ev where
  | attempt (t : TxId) (σ : State) : Ev
  | commit  (t : TxId) (σ : State) : Ev

abbrev Schedule := List Ev

/-- The semantic projection: committed transaction ids in commit
    order.  Position = logical time; the list = consumed journal
    (`sem_forced`).  Aborts and snapshots are erased. -/
def semProj : Schedule → List TxId
  | [] => []
  | .attempt _ _ :: evs => semProj evs
  | .commit t _ :: evs => t :: semProj evs

/-- An implementation artifact NOT in the semantic projection. -/
def abortCount : Schedule → Nat
  | [] => 0
  | .attempt _ _ :: evs => abortCount evs + 1
  | .commit _ _ :: evs => abortCount evs

/-- **Structural schedule equivalence** ≈_J: identical semantic
    projections.  Same commit order, same logical time assignment,
    same journal consumption; validation is enforced by trace
    legality (admissibility), not encoded in the projection; abort
    count, speculative order and snapshot choice may differ
    arbitrarily. -/
def ScheduleEquiv (evs₁ evs₂ : Schedule) : Prop :=
  semProj evs₁ = semProj evs₂

/-- Legal runs of the parallel machine, with the schedule explicit.
    Same discipline as `Par` of Lemma 3A (ordered commit +
    validation), but every speculative attempt leaves a trace event. -/
inductive RunTrace {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → Schedule → State → Out → Prop where
  | nil : RunTrace E P s o [] [] s o
  | attempt (σ : State) :
      RunTrace E P s o (t :: J) evs s' o' →
      RunTrace E P s o (t :: J) (.attempt t σ :: evs) s' o'
  | commit (σ : State) :
      validates s (runTx E t σ (P t)).2.2 →
      RunTrace E P (applyW s (runTx E t σ (P t)).1)
        (o ++ (runTx E t σ (P t)).2.1) J evs s' o' →
      RunTrace E P s o (t :: J) (.commit t σ :: evs) s' o'

/- ================================================================
   §4  Semantic layer: ≈_J ⇒ observable equivalence
   ================================================================ -/

/-- Journal consumption is forced: the semantic projection of any
    legal trace is exactly the consumed journal. -/
theorem sem_forced {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : RunTrace E P s o J evs s' o') : semProj evs = J := by
  induction h with
  | nil => rfl
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ _ _ ih => simpa [semProj] using ih

/-- Every legal trace refines the sequential fold of its own semantic
    projection. -/
theorem trace_refines_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : RunTrace E P s o J evs s' o') : EvalSeq E P s o (semProj evs) s' o' := by
  induction h with
  | nil => exact .nil
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ hval _ ih =>
      simpa [semProj] using EvalSeq.cons (commit_evalBody _ _ _ _ _ _ hval) ih

/-- **Lemma 3.5 (semantic ⇒ observable).**  Structurally equivalent
    schedules — even over different journals, with different abort
    structure and adversarial snapshots — produce the same Result,
    hence the same Observable. -/
theorem lemma3_5_equiv_implies_observable {Q : Type}
    {E : Q → TxId → Int} {P : Program Q}
    (h₁ : RunTrace E P s o J₁ evs₁ s₁ o₁)
    (h₂ : RunTrace E P s o J₂ evs₂ s₂ o₂)
    (heq : ScheduleEquiv evs₁ evs₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have e₁ := trace_refines_seq h₁
  have e₂ := trace_refines_seq h₂
  rw [heq] at e₁
  exact seq_deterministic e₁ e₂

/-- All legal complete runs of one (P, J) are pairwise ≈_J: within a
    fixed (program, journal, initial state), EVERY difference between
    legal executions is an implementation artifact. -/
theorem same_journal_all_equiv {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h₁ : RunTrace E P s o J evs₁ s₁ o₁)
    (h₂ : RunTrace E P s o J evs₂ s₂ o₂) :
    ScheduleEquiv evs₁ evs₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  have heq : ScheduleEquiv evs₁ evs₂ := by
    unfold ScheduleEquiv
    rw [sem_forced h₁, sem_forced h₂]
  exact ⟨heq, lemma3_5_equiv_implies_observable h₁ h₂ heq⟩

/- ================================================================
   §5  Witnesses: artifacts erased; converse fails
   ================================================================ -/

def E0 : Unit → TxId → Int := fun _ _ => 0
def Pdone : Program Unit := fun _ => .done
def sInit : State := fun _ => 0

/-- Abort count is an implementation artifact: two legal runs of the
    SAME (P, J, s), one clean and one with a speculative abort,
    different abortCount, still ≈_J — and identical Result. -/
theorem abort_count_artifact :
    ∃ (evs₁ evs₂ : Schedule),
      RunTrace E0 Pdone sInit [] [0] evs₁ sInit [] ∧
      RunTrace E0 Pdone sInit [] [0] evs₂ sInit [] ∧
      abortCount evs₁ ≠ abortCount evs₂ ∧
      ScheduleEquiv evs₁ evs₂ := by
  have hrun : runTx E0 0 sInit (Pdone 0) = (w₀, [], []) := by
    simp [Pdone, runTx, runInstr]
  have hcommit : RunTrace E0 Pdone sInit [] [0] [.commit 0 sInit] sInit [] := by
    refine RunTrace.commit sInit ?_ ?_
    · rw [hrun]; intro p hp; cases hp
    · rw [hrun, applyW_empty]
      simpa using RunTrace.nil
  refine ⟨[.commit 0 sInit], [.attempt 0 sInit, .commit 0 sInit],
          hcommit, RunTrace.attempt sInit hcommit, ?_, ?_⟩
  · simp [abortCount]
  · simp [ScheduleEquiv, semProj]

/-- **The converse fails** (strictness of the hierarchy):
    ¬(S₁ ≈_J S₂) does not imply different Observables.  Two runs with
    DIFFERENT semantic projections whose Observables coincide:
    equality of Observables without ≈_J is implementation
    coincidence, not semantic identity. -/
theorem observable_coincidence_not_equiv :
    ∃ (J₁ J₂ : Journal) (evs₁ evs₂ : Schedule) (r₁ r₂ : Result),
      RunTrace E0 Pdone sInit [] J₁ evs₁ r₁.1 r₁.2 ∧
      RunTrace E0 Pdone sInit [] J₂ evs₂ r₂.1 r₂.2 ∧
      ¬ ScheduleEquiv evs₁ evs₂ ∧
      Observable r₁ = Observable r₂ := by
  have hrun : ∀ t : TxId, runTx E0 t sInit (Pdone t) = (w₀, [], []) := by
    intro t; simp [Pdone, runTx, runInstr]
  have hcommit : ∀ t : TxId,
      RunTrace E0 Pdone sInit [] [t] [.commit t sInit] sInit [] := by
    intro t
    refine RunTrace.commit sInit ?_ ?_
    · rw [hrun t]; intro p hp; cases hp
    · rw [hrun t, applyW_empty]
      simpa using RunTrace.nil
  refine ⟨[0], [1], [.commit 0 sInit], [.commit 1 sInit],
          (sInit, []), (sInit, []), hcommit 0, hcommit 1, ?_, rfl⟩
  simp [ScheduleEquiv, semProj]
