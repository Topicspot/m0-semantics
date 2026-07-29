/-
  M₀ mechanization — Lemma 5 (Failure-tolerant substrate independence).

  Next research stage after v1.0, chosen per the Related Work
  conclusion ("the more distinctive direction may be to push the
  substrate interface further: a substrate with partial failure ...
  which is where the current `forced` law would have to be weakened").

  Thesis being mechanized:

      substrate independence (L4) survives the weakening of `forced`
      from equality to a PREFIX of the journal — i.e. it extends to
      substrates that may crash-stop mid-journal — and the price is
      exact: results agree not on equality of observables but on the
      PREFIX ORDER of observables.

  Construction.

  1. Sequential prefix monotonicity (§4): the reference fold is
     monotone in the journal — `runSeq_append` decomposes the fold
     over a journal concatenation, and `runSeq_out_shift` shows the
     emit stream only ever grows.  Consequence: consuming a prefix of
     the journal emits a prefix of the reference observable.  This is
     a property of Seq alone, independent of any machine.

  2. `FailSoundSubstrate` (§5) — the L4 interface with `forced`
     weakened to `forcedPrefix : proj sc <+: J`.  `refines` is
     unchanged: every legal (possibly crashed) run still refines the
     sequential fold of its own projection.  Every `SoundSubstrate`
     is a `FailSoundSubstrate` (`SoundSubstrate.toFail`) with the
     degenerate suffix [], so L4 is literally the total fragment of
     this interface: nothing in v1.0 is modified.

  3. Results (§5):
     * `fail_run_eq_seq_proj` — every legal run on every fail-sound
       substrate equals Seq of its consumed prefix (the analogue of
       `substrate_run_eq_seq`);
     * `fail_substrate_independence` — for ANY two fail-sound
       substrates, if one run's projection is a prefix of the
       other's, the observables stand in prefix order and the longer
       run factors through the shorter run's result state: crashed
       runs of different machines never DIVERGE, they only STOP;
     * `fail_substrate_independence_eq` — equal projections still
       give equal results (recovering the L4 conclusion inside the
       weaker interface);
     * `fail_observable_prefix` — crash-observable safety: the
       observable of ANY legal run on ANY fail-sound substrate is a
       prefix of the reference observable Seq(P, J).  A crash can
       truncate the output; it can never fabricate output the
       journal did not order.

  4. Substrate instance (§6): the crash-stop optimistic machine
     `CrashRun` — the trace machine of L3.5 with one new legal event:
     halting at any point with the remaining journal unconsumed.
     `crash_forced_prefix` and `crash_refines_seq` make it a
     `FailSoundSubstrate`; `runTrace_is_crashRun` embeds every total
     optimistic run, so the machine is a strict extension.

  5. Witnesses (§7): `crash_prefix_witness` — a crashed run on the
     journal [0, 1] whose projection [0] violates the L4 `forced`
     law (the weakening is strict: this machine is NOT a
     SoundSubstrate), whose observable differs from the total run's
     (crash runs are not observably equal), and IS a prefix of it
     (the new law is exactly what survives).

  What is deliberately NOT claimed: nothing here says a crashed run
  can be RESUMED (recovery is a liveness/implementation concern, out
  of X, exactly like fairness in L2); and nothing constrains WHERE a
  substrate may crash — any prefix is admissible, the theorem is
  about what the crash may have emitted.

  Self-contained: `lean Lemma5.lean`.  §0–§3 shared verbatim with
  Lemma4.lean (extended language of 3A, instrumented semantics,
  snapshot adequacy, commit realization, optimistic trace machine).
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

/-- Instrumented evaluation against snapshot σ, at logical time t. -/
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
   §3  Substrate 1: the optimistic trace machine (Lemma 3.5)
   ================================================================ -/

inductive Ev where
  | attempt (t : TxId) (σ : State) : Ev
  | commit  (t : TxId) (σ : State) : Ev

abbrev Schedule := List Ev

/-- Semantic projection of an optimistic trace (Lemma 3.5). -/
def semProj : Schedule → List TxId
  | [] => []
  | .attempt _ _ :: evs => semProj evs
  | .commit t _ :: evs => t :: semProj evs

/-- Implementation artifact of substrate 1. -/
def abortCount : Schedule → Nat
  | [] => 0
  | .attempt _ _ :: evs => abortCount evs + 1
  | .commit _ _ :: evs => abortCount evs

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

theorem sem_forced {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : RunTrace E P s o J evs s' o') : semProj evs = J := by
  induction h with
  | nil => rfl
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ _ _ ih => simpa [semProj] using ih

theorem trace_refines_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : RunTrace E P s o J evs s' o') : EvalSeq E P s o (semProj evs) s' o' := by
  induction h with
  | nil => exact .nil
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ hval _ ih =>
      simpa [semProj] using EvalSeq.cons (commit_evalBody _ _ _ _ _ _ hval) ih

/- ================================================================
   §4  Sequential prefix monotonicity (a property of Seq alone)
   ================================================================ -/

/-- The fold decomposes over journal concatenation. -/
theorem runSeq_append {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ (J₁ J₂ : Journal) (s : State) (o : Out),
      runSeq E P s o (J₁ ++ J₂)
        = runSeq E P (runSeq E P s o J₁).1 (runSeq E P s o J₁).2 J₂ := by
  intro J₁
  induction J₁ with
  | nil => intro J₂ s o; rfl
  | cons t J ih =>
      intro J₂ s o
      simp only [List.cons_append, runSeq]
      exact ih ..

/-- The emit stream only ever grows: output produced so far is carried
    through the rest of the fold verbatim. -/
theorem runSeq_out_shift {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ (J : Journal) (s : State) (o : Out),
      runSeq E P s o J = ((runSeq E P s [] J).1, o ++ (runSeq E P s [] J).2) := by
  intro J
  induction J with
  | nil => intro s o; simp [runSeq]
  | cons t J ih =>
      intro s o
      simp only [runSeq]
      rw [runBody_out_shift E t (P t) s ρ₀ o]
      rw [ih (runBody E t s ρ₀ [] (P t)).1 (o ++ (runBody E t s ρ₀ [] (P t)).2),
          ih (runBody E t s ρ₀ [] (P t)).1 (runBody E t s ρ₀ [] (P t)).2]
      simp

/-- **Sequential prefix monotonicity.**  Consuming a prefix of the
    journal emits a prefix of the reference observable.  No machine is
    mentioned: this is the reason crashes can only truncate. -/
theorem seq_out_prefix {Q : Type} (E : Q → TxId → Int) (P : Program Q)
    (s : State) (o : Out) {J₁ J₂ : Journal} (h : J₁ <+: J₂) :
    (runSeq E P s o J₁).2 <+: (runSeq E P s o J₂).2 := by
  obtain ⟨K, hK⟩ := h
  subst hK
  rw [runSeq_append E P J₁ K s o,
      runSeq_out_shift E P K (runSeq E P s o J₁).1 (runSeq E P s o J₁).2]
  exact ⟨_, rfl⟩

/- ================================================================
   §5  The weakened interface and failure-tolerant independence
   ================================================================ -/

/-- The L4 interface, verbatim (total substrates). -/
structure SoundSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) where
  Sched : Type
  Run : State → Out → Journal → Sched → State → Out → Prop
  proj : Sched → List TxId
  forced : ∀ {s o J sc s' o'}, Run s o J sc s' o' → proj sc = J
  refines : ∀ {s o J sc s' o'}, Run s o J sc s' o' → EvalSeq E P s o (proj sc) s' o'

/-- **The weakening.**  A fail-sound substrate may stop consuming the
    journal at any point (`forcedPrefix`: the projection is a PREFIX of
    the journal, not the journal), but what it did consume it must have
    computed faithfully (`refines`, unchanged from L4).  Crashing is
    legal; deviating is not. -/
structure FailSoundSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) where
  Sched : Type
  Run : State → Out → Journal → Sched → State → Out → Prop
  proj : Sched → List TxId
  forcedPrefix : ∀ {s o J sc s' o'}, Run s o J sc s' o' → proj sc <+: J
  refines : ∀ {s o J sc s' o'}, Run s o J sc s' o' → EvalSeq E P s o (proj sc) s' o'

/-- L4 substrates are the total fragment: every sound substrate is
    fail-sound with the degenerate suffix []. -/
def SoundSubstrate.toFail {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : SoundSubstrate Q E P) : FailSoundSubstrate Q E P where
  Sched := A.Sched
  Run := A.Run
  proj := A.proj
  forcedPrefix := fun h => A.forced h ▸ ⟨[], by simp⟩
  refines := A.refines

/-- Every legal run on every fail-sound substrate equals Seq of its own
    consumed prefix (analogue of `substrate_run_eq_seq`). -/
theorem fail_run_eq_seq_proj {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : FailSoundSubstrate Q E P)
    {s : State} {o : Out} {J : Journal} {sc : A.Sched} {s' : State} {o' : Out}
    (h : A.Run s o J sc s' o') :
    s' = (runSeq E P s o (A.proj sc)).1 ∧ o' = (runSeq E P s o (A.proj sc)).2 :=
  seq_deterministic (A.refines h) (runSeq_sound E P (A.proj sc) s o)

/-- **Lemma 5 (failure-tolerant substrate independence).**  For ANY two
    fail-sound substrates started identically on the same journal, if
    one run's projection is a prefix of the other's, then (i) the
    observables stand in prefix order and (ii) the longer run factors
    exactly through the shorter run's result.  Runs of different
    machines never diverge under partial failure — they only stop. -/
theorem fail_substrate_independence {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A B : FailSoundSubstrate Q E P)
    {s : State} {o : Out} {J : Journal} {a : A.Sched} {b : B.Sched}
    {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : A.Run s o J a s₁ o₁) (h₂ : B.Run s o J b s₂ o₂)
    (hpre : A.proj a <+: B.proj b) :
    o₁ <+: o₂ ∧
    ∃ K, A.proj a ++ K = B.proj b ∧
      s₂ = (runSeq E P s₁ o₁ K).1 ∧ o₂ = (runSeq E P s₁ o₁ K).2 := by
  obtain ⟨hs₁, ho₁⟩ := fail_run_eq_seq_proj A h₁
  obtain ⟨hs₂, ho₂⟩ := fail_run_eq_seq_proj B h₂
  obtain ⟨K, hK⟩ := hpre
  refine ⟨?_, K, hK, ?_, ?_⟩
  · rw [ho₁, ho₂]
    exact seq_out_prefix E P s o ⟨K, hK⟩
  · rw [hs₂, ← hK, runSeq_append E P (A.proj a) K s o, ← hs₁, ← ho₁]
  · rw [ho₂, ← hK, runSeq_append E P (A.proj a) K s o, ← hs₁, ← ho₁]

/-- Equal projections still give equal results: the L4 conclusion holds
    verbatim inside the weaker interface. -/
theorem fail_substrate_independence_eq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A B : FailSoundSubstrate Q E P)
    {s : State} {o : Out} {J₁ J₂ : Journal} {a : A.Sched} {b : B.Sched}
    {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : A.Run s o J₁ a s₁ o₁) (h₂ : B.Run s o J₂ b s₂ o₂)
    (heq : A.proj a = B.proj b) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have e₁ := A.refines h₁
  have e₂ := B.refines h₂
  rw [heq] at e₁
  exact seq_deterministic e₁ e₂

/-- Conservativity: L4 substrate independence re-derived through the
    weaker interface — the strengthening changes no v1.0 statement. -/
theorem substrate_independence_of_fail {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A B : SoundSubstrate Q E P)
    {s : State} {o : Out} {J₁ J₂ : Journal} {a : A.Sched} {b : B.Sched}
    {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : A.Run s o J₁ a s₁ o₁) (h₂ : B.Run s o J₂ b s₂ o₂)
    (heq : A.proj a = B.proj b) :
    s₁ = s₂ ∧ o₁ = o₂ :=
  fail_substrate_independence_eq A.toFail B.toFail h₁ h₂ heq

/-- **Crash-observable safety.**  The observable of ANY legal run on
    ANY fail-sound substrate is a prefix of the reference observable
    Seq(P, J): a crash may truncate the output, it can never fabricate
    output the journal did not order.  This is the failure-tolerant
    form of X. -/
theorem fail_observable_prefix {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : FailSoundSubstrate Q E P)
    {s : State} {o : Out} {J : Journal} {sc : A.Sched} {s' : State} {o' : Out}
    (h : A.Run s o J sc s' o') :
    o' <+: (runSeq E P s o J).2 := by
  obtain ⟨_, ho⟩ := fail_run_eq_seq_proj A h
  rw [ho]
  exact seq_out_prefix E P s o (A.forcedPrefix h)

/- ================================================================
   §6  Instance: the crash-stop optimistic machine
   ================================================================ -/

/-- The trace machine of L3.5 with ONE new legal behaviour: halting at
    any point with the remaining journal unconsumed (`crash` is `nil`
    with the journal argument generalized from [] to J).  Everything
    else — speculation, adversarial snapshots, validation, ordered
    commit — is unchanged. -/
inductive CrashRun {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → Schedule → State → Out → Prop where
  | crash : CrashRun E P s o J [] s o
  | attempt (σ : State) :
      CrashRun E P s o (t :: J) evs s' o' →
      CrashRun E P s o (t :: J) (.attempt t σ :: evs) s' o'
  | commit (σ : State) :
      validates s (runTx E t σ (P t)).2.2 →
      CrashRun E P (applyW s (runTx E t σ (P t)).1)
        (o ++ (runTx E t σ (P t)).2.1) J evs s' o' →
      CrashRun E P s o (t :: J) (.commit t σ :: evs) s' o'

/-- The projection of a crashed run is a prefix of the journal. -/
theorem crash_forced_prefix {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    {s : State} {o : Out} {J : Journal} {evs : Schedule} {s' : State} {o' : Out}
    (h : CrashRun E P s o J evs s' o') : semProj evs <+: J := by
  induction h with
  | crash => exact ⟨_, rfl⟩
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ _ _ ih =>
      obtain ⟨K, hK⟩ := ih
      exact ⟨K, by simp [semProj, hK]⟩

/-- What a crashed run did consume, it computed faithfully. -/
theorem crash_refines_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    {s : State} {o : Out} {J : Journal} {evs : Schedule} {s' : State} {o' : Out}
    (h : CrashRun E P s o J evs s' o') : EvalSeq E P s o (semProj evs) s' o' := by
  induction h with
  | crash => exact .nil
  | attempt σ _ ih => simpa [semProj] using ih
  | commit σ hval _ ih =>
      simpa [semProj] using EvalSeq.cons (commit_evalBody _ _ _ _ _ _ hval) ih

/-- The crash-stop optimistic machine is a fail-sound substrate. -/
def crashOptimisticSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) :
    FailSoundSubstrate Q E P where
  Sched := Schedule
  Run := CrashRun E P
  proj := semProj
  forcedPrefix := crash_forced_prefix
  refines := crash_refines_seq

/-- Strict extension: every total optimistic run is a legal crash-stop
    run (that happens not to crash). -/
theorem runTrace_is_crashRun {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    {s : State} {o : Out} {J : Journal} {evs : Schedule} {s' : State} {o' : Out}
    (h : RunTrace E P s o J evs s' o') : CrashRun E P s o J evs s' o' := by
  induction h with
  | nil => exact .crash
  | attempt σ _ ih => exact .attempt σ ih
  | commit σ hval _ ih => exact .commit σ hval ih

/- ================================================================
   §7  Witness
   ================================================================ -/

def E0 : Unit → TxId → Int := fun _ _ => 0
def sInit : State := fun _ => 0

/-- Two emitting transactions: the observable makes truncation visible. -/
def Pemit : Program Unit
  | 0 => .emit (.const 10) .done
  | _ => .emit (.const 20) .done

/-- **Witness for the strictness and exactness of the weakening.**  On
    the journal [0, 1] the crash-stop machine legally halts after
    committing only tx 0:
    * its projection [0] is NOT the journal — the L4 `forced` law fails,
      so this machine is not a SoundSubstrate (the weakening is strict);
    * its observable [10] is NOT the total observable [10, 20] — crashed
      runs are not observably equal (equality is genuinely lost);
    * its observable IS a prefix of the total observable — the prefix
      law is exactly what survives. -/
theorem crash_prefix_witness :
    ∃ (evs evsTot : Schedule) (s₁ s₂ : State) (o₁ o₂ : Out),
      CrashRun E0 Pemit sInit [] [0, 1] evs s₁ o₁ ∧
      RunTrace E0 Pemit sInit [] [0, 1] evsTot s₂ o₂ ∧
      semProj evs ≠ [0, 1] ∧
      o₁ ≠ o₂ ∧
      o₁ <+: o₂ := by
  have h₁ : CrashRun E0 Pemit sInit [] [0, 1] [.commit 0 sInit]
      (applyW sInit w₀) [10] :=
    CrashRun.commit sInit (fun p hp => nomatch hp) CrashRun.crash
  have h₂ : RunTrace E0 Pemit sInit [] [0, 1] [.commit 0 sInit, .commit 1 sInit]
      (applyW (applyW sInit w₀) w₀) [10, 20] :=
    RunTrace.commit sInit (fun p hp => nomatch hp)
      (RunTrace.commit sInit (fun p hp => nomatch hp) RunTrace.nil)
  refine ⟨_, _, _, _, _, _, h₁, h₂, ?_, ?_, ⟨[20], rfl⟩⟩
  · simp [semProj]
  · simp

/-- Sanity: the crash observable [10] is what `fail_observable_prefix`
    promises — a prefix of the reference Seq(Pemit, [0,1]) observable. -/
theorem crash_prefix_witness_vs_seq :
    ∃ (evs : Schedule) (s' : State) (o' : Out),
      CrashRun E0 Pemit sInit [] [0, 1] evs s' o' ∧
      o' <+: (runSeq E0 Pemit sInit [] [0, 1]).2 := by
  have h : CrashRun E0 Pemit sInit [] [0, 1] [.commit 0 sInit]
      (applyW sInit w₀) [10] :=
    CrashRun.commit sInit (fun p hp => nomatch hp) CrashRun.crash
  exact ⟨_, _, _, h,
    fail_observable_prefix (crashOptimisticSubstrate Unit E0 Pemit) h⟩

/- ================================================================
   §8  Completeness (realizability, as in L4 — NOT liveness)
   ================================================================ -/

def FailSubstrateComplete {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : FailSoundSubstrate Q E P) : Prop :=
  ∀ s o J, ∃ (sc : A.Sched) (s' : State) (o' : Out), A.Run s o J sc s' o'

/-- The crash machine is complete — trivially (it may crash at once),
    but also non-vacuously: by `runTrace_is_crashRun` every total
    optimistic run is legal, so completeness of L4's substrate 1
    transfers.  Stated with the immediate witness. -/
theorem crash_complete {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    FailSubstrateComplete (crashOptimisticSubstrate Q E P) :=
  fun s o _ => ⟨[], s, o, .crash⟩
