/-
  M₀ mechanization — Lemma 4 (Substrate independence).

  Thesis being mechanized (owner's formulation after L3.5): not

      "this particular M₀ machine ports to another substrate"

  but

      "ANY substrate that realizes the same semantic closure is a
       realization of M₀."

  Construction.

  1. `SoundSubstrate` — the formal meaning of "realizes the semantic
     closure".  A substrate is an arbitrary type of schedules `Sched`,
     a legal-run relation `Run`, and a semantic projection
     `proj : Sched → List TxId`, subject to two laws:
       * `forced`  — the projection of a legal run is exactly the
                     consumed journal (journal consumption is not
                     up to the substrate);
       * `refines` — every legal run refines the sequential fold of
                     its own projection (the denotation `Seq`).
     This is the ≈_J invariant of L3.5 promoted to an interface:
     schedule equivalence extends ACROSS substrates as equality of
     semantic projections.

  2. Substrate 1 (optimistic): the trace machine of Lemma 3.5 —
     speculation, adversarial snapshots, validation, ordered commit.
     Its implementation artifacts: abort count, snapshot choice.

  3. Substrate 2 (wavefront, NEW): a pessimistic BSP-style machine
     with a genuinely different operational structure:
       * static conflict analysis on syntactic footprints
         (`cellsOf` — the cells a body can possibly touch);
       * the journal is consumed in WAVES of pairwise non-conflicting
         transactions;
       * every transaction of a wave executes against the SAME
         wave-entry state (no snapshots, no validation, no aborts —
         conflicts are excluded statically, not detected dynamically);
       * write sets are merged at the wave barrier; emits are
         concatenated in journal order.
     Its implementation artifacts: the wave PARTITION (how the journal
     is cut into waves) — a vocabulary of artifacts entirely disjoint
     from substrate 1's.

  Results:

  * `substrate_independence` — for ANY two sound substrates A, B and
    legal runs with equal semantic projections, the Results (hence
    Observables) coincide.  ≈_J is the transfer invariant; it does not
    mention either machine's internals.
  * `substrate_run_eq_seq` — every legal run on every sound substrate
    equals Seq(P,J): M₀ is the equivalence class, substrates are its
    representatives.
  * `optimisticSubstrate`, `wavefrontSubstrate` — both machines are
    instances of `SoundSubstrate`.  For the wavefront machine the
    substance is `wave_refines_seq_aux`: a non-interference (frame)
    theorem — disjoint static footprints imply that executing a whole
    wave against its entry state realizes the sequential fold.  Proved
    from the L2/L3 snapshot-adequacy kernel: the read set of a body is
    contained in its footprint (`runInstr_rs_cells`) and its writes
    stay inside its footprint (`runInstr_writes_frame`).
  * `cross_substrate_same_journal` — concretely: an optimistic run and
    a wavefront run of the same (P, J, s₀) always agree.
  * `wave_progress` — the wavefront machine is total (singleton waves
    always legal: sequential execution is the degenerate wave run).
  * `wave_partition_artifact` — witness: two legal wavefront runs of
    the same (P, J) with DIFFERENT partitions (one two-transaction
    parallel wave vs two sequential waves), same semantic projection —
    partitioning is an implementation artifact, exactly like abort
    count on substrate 1.
  * `cross_substrate_witness` — end-to-end witness: an optimistic run
    WITH an abort and a single-wave parallel wavefront run of the same
    (P, J) produce identical Results.  Two different machines, two
    different artifact vocabularies, one semantics.

  Self-contained: `lean Lemma4.lean`.  §0–§2 shared verbatim with
  Lemma3.lean / Lemma3_5.lean (extended language of 3A, instrumented
  semantics, snapshot adequacy, commit realization); §3 shared with
  Lemma3_5.lean (optimistic trace machine).
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
   §4  Static footprints and frame theorems
   ================================================================ -/

/-- Syntactic footprint: every cell a body can possibly touch (both
    branches of `ite` counted — a sound over-approximation computed
    WITHOUT executing the body: this is what makes the second
    substrate pessimistic/static rather than optimistic/dynamic). -/
def cellsOf {Q : Type} : Body Q → List Cell
  | .done => []
  | .read c _ k => c :: cellsOf k
  | .write c _ k => c :: cellsOf k
  | .emit _ k => cellsOf k
  | .ite _ b₁ b₂ => cellsOf b₁ ++ cellsOf b₂
  | .ext _ _ k => cellsOf k

/-- The read set stays inside the footprint. -/
theorem runInstr_rs_cells {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b σ w ρ o rs p, p ∈ (runInstr E t σ w ρ o rs b).2.2 →
      p ∈ rs ∨ p.1 ∈ cellsOf b := by
  intro b
  induction b with
  | done => intro σ w ρ o rs p hp; exact .inl (by simpa [runInstr] using hp)
  | read c x k ih =>
      intro σ w ρ o rs p hp
      cases hw : w c with
      | some v =>
          rcases ih σ w (updEnv ρ x v) o rs p (by simpa [runInstr, hw] using hp) with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)
      | none   =>
          have hp' : p ∈ (runInstr E t σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k).2.2 := by
            simpa [runInstr, hw] using hp
          rcases ih σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) p hp' with h | h
          · rcases List.mem_append.mp h with h | h
            · exact .inl h
            · right
              have : p = (c, σ c) := by simpa using h
              subst this
              exact List.mem_cons_self ..
          · exact .inr (List.mem_cons_of_mem _ h)
  | write c e k ih =>
      intro σ w ρ o rs p hp
      rcases ih σ (updW w c (evalExpr ρ e)) ρ o rs p (by simpa [runInstr] using hp) with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
  | emit e k ih =>
      intro σ w ρ o rs p hp
      exact ih σ w ρ (o ++ [evalExpr ρ e]) rs p (by simpa [runInstr] using hp)
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro σ w ρ o rs p hp
      by_cases hc : evalExpr ρ e = 0
      · rcases ih₂ σ w ρ o rs p (by simpa [runInstr, hc] using hp) with h | h
        · exact .inl h
        · exact .inr (List.mem_append_right _ h)
      · rcases ih₁ σ w ρ o rs p (by simpa [runInstr, hc] using hp) with h | h
        · exact .inl h
        · exact .inr (List.mem_append_left _ h)
  | ext q x k ih =>
      intro σ w ρ o rs p hp
      exact ih σ w (updEnv ρ x (E q t)) o rs p (by simpa [runInstr] using hp)

/-- The writes stay inside the footprint. -/
theorem runInstr_writes_frame {Q : Type} (E : Q → TxId → Int) (t : TxId) :
    ∀ b σ w ρ o rs c, c ∉ cellsOf b → (runInstr E t σ w ρ o rs b).1 c = w c := by
  intro b
  induction b with
  | done => intro σ w ρ o rs c _; rfl
  | read c' x k ih =>
      intro σ w ρ o rs c hc
      have hk : c ∉ cellsOf k := fun h => hc (List.mem_cons_of_mem _ h)
      cases hw : w c' with
      | some v => simpa [runInstr, hw] using ih σ w (updEnv ρ x v) o rs c hk
      | none   =>
          simpa [runInstr, hw] using ih σ w (updEnv ρ x (σ c')) o (rs ++ [(c', σ c')]) c hk
  | write c' e k ih =>
      intro σ w ρ o rs c hc
      have hne : c ≠ c' := fun h => hc (h ▸ List.mem_cons_self ..)
      have hk : c ∉ cellsOf k := fun h => hc (List.mem_cons_of_mem _ h)
      have hrec := ih σ (updW w c' (evalExpr ρ e)) ρ o rs c hk
      simpa [runInstr, updW, hne] using hrec
  | emit e k ih =>
      intro σ w ρ o rs c hc
      simpa [runInstr] using ih σ w ρ (o ++ [evalExpr ρ e]) rs c hc
  | ite e b₁ b₂ ih₁ ih₂ =>
      intro σ w ρ o rs c hc
      have h₁ : c ∉ cellsOf b₁ := fun h => hc (List.mem_append_left _ h)
      have h₂ : c ∉ cellsOf b₂ := fun h => hc (List.mem_append_right _ h)
      by_cases hcnd : evalExpr ρ e = 0
      · simpa [runInstr, hcnd] using ih₂ σ w ρ o rs c h₂
      · simpa [runInstr, hcnd] using ih₁ σ w ρ o rs c h₁
  | ext q x k ih =>
      intro σ w ρ o rs c hc
      simpa [runInstr] using ih σ w (updEnv ρ x (E q t)) o rs c hc

/-- Agreement of two states on a set of cells. -/
def agreeOn (S₀ S : State) (cs : List Cell) : Prop := ∀ c ∈ cs, S c = S₀ c

/-- Frame validation: a state that agrees with the wave-entry state on
    a body's footprint validates the read set produced at wave entry.
    This is where static conflict analysis meets the dynamic
    validation kernel of L2: agreement on the OVER-approximation
    implies agreement on the actual reads. -/
theorem frame_validates {Q : Type} (E : Q → TxId → Int) (t : TxId)
    (b : Body Q) (S₀ S : State) (h : agreeOn S₀ S (cellsOf b)) :
    validates S (runTx E t S₀ b).2.2 := by
  intro p hp
  have hcell : p ∈ ([] : ReadSet) ∨ p.1 ∈ cellsOf b :=
    runInstr_rs_cells E t b S₀ w₀ ρ₀ [] [] p hp
  have hsnap : p ∈ ([] : ReadSet) ∨ S₀ p.1 = p.2 :=
    runInstr_rs_from_snapshot E t b S₀ w₀ ρ₀ [] [] p hp
  rcases hcell with h0 | hcell
  · cases h0
  rcases hsnap with h0 | hsnap
  · cases h0
  rw [h p.1 hcell, hsnap]

/- ================================================================
   §5  Substrate 2: the wavefront (pessimistic BSP) machine
   ================================================================ -/

/-- Pairwise non-conflicting wave (relative to program P): the head's
    footprint is disjoint from every later footprint, recursively. -/
def DisjCells (xs ys : List Cell) : Prop := ∀ c ∈ xs, c ∉ ys

inductive WaveOk {Q : Type} (P : Program Q) : List TxId → Prop where
  | nil : WaveOk P []
  | cons {t : TxId} {ts : List TxId} :
      (∀ u ∈ ts, DisjCells (cellsOf (P t)) (cellsOf (P u))) →
      WaveOk P ts → WaveOk P (t :: ts)

/-- Combined footprint of a wave. -/
def wcells {Q : Type} (P : Program Q) : List TxId → List Cell
  | [] => []
  | t :: ts => cellsOf (P t) ++ wcells P ts

/-- Wave exit state: every transaction executes against the FIXED
    wave-entry state S₀; write sets are merged at the barrier. -/
def waveApply {Q : Type} (E : Q → TxId → Int) (P : Program Q) (S₀ : State) :
    State → List TxId → State
  | S, [] => S
  | S, t :: ts => waveApply E P S₀ (applyW S (runTx E t S₀ (P t)).1) ts

/-- Wave output: emits concatenated in journal order (the merge at the
    barrier is deterministic regardless of physical execution order). -/
def waveOut {Q : Type} (E : Q → TxId → Int) (P : Program Q) (S₀ : State) :
    List TxId → Out
  | [] => []
  | t :: ts => (runTx E t S₀ (P t)).2.1 ++ waveOut E P S₀ ts

/-- The wavefront machine: the journal is consumed in statically
    non-conflicting waves.  No snapshots, no validation, no aborts —
    a genuinely different operational structure from substrate 1. -/
inductive WaveRun {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    State → Out → Journal → List (List TxId) → State → Out → Prop where
  | nil : WaveRun E P s o [] [] s o
  | wave (ts : List TxId) :
      WaveOk P ts →
      WaveRun E P (waveApply E P s s ts) (o ++ waveOut E P s ts) J ws s' o' →
      WaveRun E P s o (ts ++ J) (ts :: ws) s' o'

/-- Semantic projection of a wavefront schedule: the wave partition is
    erased, only journal consumption in order remains. -/
def waveProj : List (List TxId) → List TxId
  | [] => []
  | ts :: ws => ts ++ waveProj ws

theorem wave_forced {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : WaveRun E P s o J ws s' o') : waveProj ws = J := by
  induction h with
  | nil => rfl
  | wave ts _ _ ih => simpa [waveProj] using ih

/-- Cells of later wave members avoid the head's footprint. -/
theorem wcells_disjoint_head {Q : Type} {P : Program Q} {t : TxId} :
    ∀ {ts : List TxId}, (∀ u ∈ ts, DisjCells (cellsOf (P t)) (cellsOf (P u))) →
    ∀ c ∈ wcells P ts, c ∉ cellsOf (P t) := by
  intro ts
  induction ts with
  | nil => intro _ c hc; cases hc
  | cons u us ih =>
      intro hd c hc hct
      rcases List.mem_append.mp hc with h | h
      · exact hd u (List.mem_cons_self ..) c hct h
      · exact ih (fun v hv => hd v (List.mem_cons_of_mem _ hv)) c h hct

theorem seq_append {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h₁ : EvalSeq E P s o ts s' o') (h₂ : EvalSeq E P s' o' J s'' o'') :
    EvalSeq E P s o (ts ++ J) s'' o'' := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hb _ ih => exact .cons hb (ih h₂)

/-- **Non-interference (frame) theorem — the substance of substrate 2.**
    A statically non-conflicting wave, executed entirely against its
    entry state S₀ with a barrier merge, realizes the sequential fold:
    for any current state S agreeing with S₀ on the wave's combined
    footprint, the merged result IS the sequential execution. -/
theorem wave_refines_seq_aux {Q : Type} (E : Q → TxId → Int) (P : Program Q)
    (S₀ : State) :
    ∀ {ts : List TxId}, WaveOk P ts →
    ∀ (S : State) (o : Out), agreeOn S₀ S (wcells P ts) →
      EvalSeq E P S o ts (waveApply E P S₀ S ts) (o ++ waveOut E P S₀ ts) := by
  intro ts hok
  induction hok with
  | nil => intro S o _; simpa [waveApply, waveOut] using EvalSeq.nil (E := E) (P := P)
  | @cons t ts hd htl ih =>
      intro S o hagree
      have hagree_head : agreeOn S₀ S (cellsOf (P t)) :=
        fun c hc => hagree c (List.mem_append_left _ hc)
      have hval : validates S (runTx E t S₀ (P t)).2.2 :=
        frame_validates E t (P t) S₀ S hagree_head
      have step : EvalBody E t S ρ₀ o (P t)
          (applyW S (runTx E t S₀ (P t)).1) (o ++ (runTx E t S₀ (P t)).2.1) :=
        commit_evalBody E t S (P t) o S₀ hval
      have hagree' : agreeOn S₀ (applyW S (runTx E t S₀ (P t)).1) (wcells P ts) := by
        intro c hc
        have hnt : c ∉ cellsOf (P t) := wcells_disjoint_head hd c hc
        have hw : (runTx E t S₀ (P t)).1 c = none := by
          have := runInstr_writes_frame E t (P t) S₀ w₀ ρ₀ [] [] c hnt
          simpa [runTx, w₀] using this
        have hfix : applyW S (runTx E t S₀ (P t)).1 c = S c := by
          simp [applyW, hw]
        rw [hfix]
        exact hagree c (List.mem_append_right _ hc)
      have tail := ih (applyW S (runTx E t S₀ (P t)).1)
        (o ++ (runTx E t S₀ (P t)).2.1) hagree'
      have goal := EvalSeq.cons step tail
      simpa [waveApply, waveOut, List.append_assoc] using goal

/-- Every legal wavefront run refines the sequential fold of its own
    semantic projection. -/
theorem wave_refines_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (h : WaveRun E P s o J ws s' o') : EvalSeq E P s o (waveProj ws) s' o' := by
  induction h with
  | nil => exact .nil
  | wave ts hok _ ih =>
      exact seq_append
        (wave_refines_seq_aux E P _ hok _ _ (fun c _ => rfl)) ih

/-- The wavefront machine is total: singleton waves are always legal,
    so sequential execution is its degenerate run.  (Analogue of
    par_progress on substrate 1.) -/
theorem wave_progress {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ J s o, ∃ ws s' o', WaveRun E P s o J ws s' o' := by
  intro J
  induction J with
  | nil => intro s o; exact ⟨[], s, o, .nil⟩
  | cons t J ih =>
      intro s o
      obtain ⟨ws, s', o', h⟩ := ih (waveApply E P s s [t]) (o ++ waveOut E P s [t])
      refine ⟨[t] :: ws, s', o', ?_⟩
      have hok : WaveOk P [t] := .cons (fun u hu => by cases hu) .nil
      exact WaveRun.wave [t] hok h

/- ================================================================
   §6  Substrate independence
   ================================================================ -/

/-- **What it means to realize the semantic closure.**  A substrate is
    ANY machine whose legal runs (i) consume exactly the journal and
    (ii) refine the sequential fold of their own semantic projection.
    ≈_J of Lemma 3.5, promoted from one machine to an interface: the
    projection is the entire semantic content of a schedule; the
    substrate's internal event vocabulary is unconstrained. -/
structure SoundSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) where
  Sched : Type
  Run : State → Out → Journal → Sched → State → Out → Prop
  proj : Sched → List TxId
  forced : ∀ {s o J sc s' o'}, Run s o J sc s' o' → proj sc = J
  refines : ∀ {s o J sc s' o'}, Run s o J sc s' o' → EvalSeq E P s o (proj sc) s' o'

/-- Substrate 1: optimistic speculation + validation + ordered commit. -/
def optimisticSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) :
    SoundSubstrate Q E P where
  Sched := Schedule
  Run := RunTrace E P
  proj := semProj
  forced := sem_forced
  refines := trace_refines_seq

/-- Substrate 2: pessimistic static conflict analysis + BSP waves. -/
def wavefrontSubstrate (Q : Type) (E : Q → TxId → Int) (P : Program Q) :
    SoundSubstrate Q E P where
  Sched := List (List TxId)
  Run := WaveRun E P
  proj := waveProj
  forced := wave_forced
  refines := wave_refines_seq

/-- **Lemma 4 (substrate independence).**  Cross-substrate ≈_J: legal
    runs of ANY two sound substrates with equal semantic projections
    produce the same Result, hence the same Observable.  The transfer
    invariant mentions no machine internals — only the projection. -/
theorem substrate_independence {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A B : SoundSubstrate Q E P)
    {s : State} {o : Out} {J₁ J₂ : Journal} {a : A.Sched} {b : B.Sched}
    {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : A.Run s o J₁ a s₁ o₁) (h₂ : B.Run s o J₂ b s₂ o₂)
    (heq : A.proj a = B.proj b) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have e₁ := A.refines h₁
  have e₂ := B.refines h₂
  rw [heq] at e₁
  exact seq_deterministic e₁ e₂

/-- Every legal run on every sound substrate is Seq(P,J): M₀ is the
    equivalence class of substrates; each machine is a representative. -/
theorem substrate_run_eq_seq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : SoundSubstrate Q E P)
    {s : State} {o : Out} {J : Journal} {a : A.Sched} {s' : State} {o' : Out}
    (h : A.Run s o J a s' o') :
    s' = (runSeq E P s o J).1 ∧ o' = (runSeq E P s o J).2 := by
  have e := A.refines h
  rw [A.forced h] at e
  exact seq_deterministic e (runSeq_sound E P J s o)

/-- Concrete corollary: an optimistic run and a wavefront run of the
    same (P, J, s₀) always agree — schedules from DIFFERENT machines
    are ≈_J whenever they consume the same journal. -/
theorem cross_substrate_same_journal {Q : Type} {E : Q → TxId → Int}
    {P : Program Q} {s : State} {o : Out} {J : Journal}
    {evs : Schedule} {ws : List (List TxId)}
    {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : RunTrace E P s o J evs s₁ o₁)
    (h₂ : WaveRun E P s o J ws s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ :=
  substrate_independence (optimisticSubstrate Q E P) (wavefrontSubstrate Q E P)
    h₁ h₂ (by show semProj evs = waveProj ws; rw [sem_forced h₁, wave_forced h₂])

/- ================================================================
   §7  Witnesses
   ================================================================ -/

def E0 : Unit → TxId → Int := fun _ _ => 0
def sInit : State := fun _ => 0

/-- Two independent writers: footprints {"a"} and {"b"} are disjoint,
    so [0, 1] is a legal parallel wave on substrate 2. -/
def Ppar : Program Unit
  | 0 => .write "a" (.const 1) .done
  | _ => .write "b" (.const 2) .done

theorem ppar_disj : DisjCells (cellsOf (Ppar 0)) (cellsOf (Ppar 1)) := by
  intro c hc
  have hc' : c = "a" := by
    cases hc with
    | head => rfl
    | tail _ h => cases h
  subst hc'
  intro hmem
  have hne : ("a" : String) ≠ "b" := by decide
  rcases List.mem_cons.mp hmem with h | h
  · exact hne h
  · cases h

theorem ppar_waveok : WaveOk Ppar [0, 1] := by
  refine .cons ?_ (.cons (fun u hu => by cases hu) .nil)
  intro u hu
  have : u = 1 := by simpa using hu
  subst this
  exact ppar_disj

/-- **Wave partition is an implementation artifact** (substrate 2's
    analogue of L3.5's `abort_count_artifact`): the same (P, J, s₀)
    runs legally as ONE parallel two-transaction wave and as TWO
    sequential singleton waves — different partitions, same semantic
    projection, and (by `substrate_run_eq_seq`) the same Result. -/
theorem wave_partition_artifact :
    ∃ (ws₁ ws₂ : List (List TxId)) (s₁ s₂ : State) (o₁ o₂ : Out),
      WaveRun E0 Ppar sInit [] [0, 1] ws₁ s₁ o₁ ∧
      WaveRun E0 Ppar sInit [] [0, 1] ws₂ s₂ o₂ ∧
      ws₁ ≠ ws₂ ∧ waveProj ws₁ = waveProj ws₂ ∧
      s₁ = s₂ ∧ o₁ = o₂ := by
  -- one parallel wave
  have h₁ : WaveRun E0 Ppar sInit [] [0, 1] [[0, 1]]
      (waveApply E0 Ppar sInit sInit [0, 1]) ([] ++ waveOut E0 Ppar sInit [0, 1]) := by
    have := WaveRun.wave (E := E0) (P := Ppar) (s := sInit) (o := [])
      (J := []) (ws := []) [0, 1] ppar_waveok .nil
    simpa using this
  -- two sequential singleton waves
  have hok1 : WaveOk Ppar [0] := .cons (fun u hu => by cases hu) .nil
  have hok2 : WaveOk Ppar [1] := .cons (fun u hu => by cases hu) .nil
  have h₂ : WaveRun E0 Ppar sInit [] [0, 1] [[0], [1]]
      (waveApply E0 Ppar (waveApply E0 Ppar sInit sInit [0])
        (waveApply E0 Ppar sInit sInit [0]) [1])
      (([] ++ waveOut E0 Ppar sInit [0]) ++
        waveOut E0 Ppar (waveApply E0 Ppar sInit sInit [0]) [1]) := by
    have tail := WaveRun.wave (E := E0) (P := Ppar)
      (s := waveApply E0 Ppar sInit sInit [0])
      (o := [] ++ waveOut E0 Ppar sInit [0]) (J := []) (ws := []) [1] hok2 .nil
    have head := WaveRun.wave (E := E0) (P := Ppar) (s := sInit) (o := [])
      (J := [1]) (ws := [[1]]) [0] hok1 (by simpa using tail)
    simpa using head
  obtain ⟨hs, ho⟩ :=
    substrate_independence (wavefrontSubstrate Unit E0 Ppar)
      (wavefrontSubstrate Unit E0 Ppar) h₁ h₂
      (by show waveProj [[0, 1]] = waveProj [[0], [1]]
          rw [wave_forced h₁, wave_forced h₂])
  exact ⟨[[0, 1]], [[0], [1]], _, _, _, _, h₁, h₂, by simp, by simp [waveProj], hs, ho⟩

/-- **Cross-substrate witness**: an optimistic run WITH a speculative
    abort and a single parallel wave of the wavefront machine — two
    machines, disjoint artifact vocabularies (abort count vs wave
    partition), identical Result. -/
theorem cross_substrate_witness :
    ∃ (evs : Schedule) (ws : List (List TxId)) (s₁ s₂ : State) (o₁ o₂ : Out),
      RunTrace E0 Ppar sInit [] [0, 1] evs s₁ o₁ ∧
      WaveRun E0 Ppar sInit [] [0, 1] ws s₂ o₂ ∧
      abortCount evs = 1 ∧ ws = [[0, 1]] ∧
      s₁ = s₂ ∧ o₁ = o₂ := by
  -- optimistic run: abort once on tx 0, then commit both (adversarial
  -- snapshot sInit both times; bodies read nothing, so validation is
  -- trivial)
  have hrun0 : runTx E0 0 sInit (Ppar 0) = (updW w₀ "a" 1, [], []) := by
    simp [Ppar, runTx, runInstr, evalExpr]
  have hrun1 : ∀ σ : State, runTx E0 1 σ (Ppar 1) = (updW w₀ "b" 2, [], []) := by
    intro σ; simp [Ppar, runTx, runInstr, evalExpr]
  have h₁ : RunTrace E0 Ppar sInit [] [0, 1]
      [.attempt 0 sInit, .commit 0 sInit, .commit 1 sInit]
      (applyW (applyW sInit (updW w₀ "a" 1)) (updW w₀ "b" 2)) [] := by
    refine RunTrace.attempt sInit ?_
    refine RunTrace.commit sInit ?_ ?_
    · rw [hrun0]; intro p hp; cases hp
    · rw [hrun0]
      refine RunTrace.commit (t := 1) sInit ?_ ?_
      · rw [hrun1]; intro p hp; cases hp
      · rw [hrun1]
        simpa using RunTrace.nil (E := E0) (P := Ppar)
  -- wavefront run: one parallel wave
  have h₂ : WaveRun E0 Ppar sInit [] [0, 1] [[0, 1]]
      (waveApply E0 Ppar sInit sInit [0, 1]) ([] ++ waveOut E0 Ppar sInit [0, 1]) := by
    have := WaveRun.wave (E := E0) (P := Ppar) (s := sInit) (o := [])
      (J := []) (ws := []) [0, 1] ppar_waveok .nil
    simpa using this
  obtain ⟨hs, ho⟩ := cross_substrate_same_journal h₁ h₂
  exact ⟨_, _, _, _, _, _, h₁, h₂, by simp [abortCount], rfl, hs, ho⟩

/- ================================================================
   §8  Completeness (realizability — deliberately NOT liveness)
   ================================================================ -/

/-- Completeness of a substrate: every (state, out, journal) admits at
    least one legal run — "every M₀ commit trace is realizable".
    This is EXISTENTIAL realizability.  The interface deliberately
    does NOT require that every legal schedule terminates: unbounded
    attempt loops remain legal on the optimistic machine.  Demanding
    termination of all legal schedules would smuggle liveness into X,
    which is a pure safety property; fairness stays out of the model. -/
def SubstrateComplete {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A : SoundSubstrate Q E P) : Prop :=
  ∀ s o J, ∃ (sc : A.Sched) (s' : State) (o' : Out), A.Run s o J sc s' o'

/-- The optimistic machine is complete: committing each transaction
    with the CURRENT state as snapshot always validates (reads taken
    from the snapshot trivially agree with it). -/
theorem trace_progress {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    ∀ J s o, ∃ evs s' o', RunTrace E P s o J evs s' o' := by
  intro J
  induction J with
  | nil => intro s o; exact ⟨[], s, o, .nil⟩
  | cons t J ih =>
      intro s o
      have hval : validates s (runTx E t s (P t)).2.2 := by
        intro p hp
        rcases runInstr_rs_from_snapshot E t (P t) s w₀ ρ₀ [] [] p hp with h | h
        · cases h
        · exact h
      obtain ⟨evs, s', o', h⟩ :=
        ih (applyW s (runTx E t s (P t)).1) (o ++ (runTx E t s (P t)).2.1)
      exact ⟨.commit t s :: evs, s', o', .commit s hval h⟩

theorem optimistic_complete {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    SubstrateComplete (optimisticSubstrate Q E P) := by
  intro s o J
  obtain ⟨evs, s', o', h⟩ := trace_progress E P J s o
  exact ⟨evs, s', o', h⟩

theorem wavefront_complete {Q : Type} (E : Q → TxId → Int) (P : Program Q) :
    SubstrateComplete (wavefrontSubstrate Q E P) := by
  intro s o J
  obtain ⟨ws, s', o', h⟩ := wave_progress E P J s o
  exact ⟨ws, s', o', h⟩

/-- ImplementsM₀ in the reviewer's sense: sound (forced + refines,
    i.e. the admissibility invariant and refinement of Seq) AND
    complete (every commit trace realizable).  Between any two such
    substrates, execution results coincide on every (P, J) — from
    soundness alone; completeness guarantees the statement is not
    vacuous. -/
theorem implements_M0_execute_eq {Q : Type} {E : Q → TxId → Int} {P : Program Q}
    (A B : SoundSubstrate Q E P)
    (_ : SubstrateComplete A) (_ : SubstrateComplete B)
    {s : State} {o : Out} {J : Journal}
    {a : A.Sched} {b : B.Sched} {s₁ s₂ : State} {o₁ o₂ : Out}
    (h₁ : A.Run s o J a s₁ o₁) (h₂ : B.Run s o J b s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have e₁ := A.refines h₁
  have e₂ := B.refines h₂
  rw [A.forced h₁] at e₁
  rw [B.forced h₂] at e₂
  exact seq_deterministic e₁ e₂
