/-
  M₀ mechanization — Lemma 2 (Commit-order theorem). THE HEART.

  Statement (canonical, per project continuation prompt §6):
    if  (1) commits happen strictly in journal order,
        (2) a commit is accepted only with a valid snapshot
            (every value the body read is still the committed value),
        (3) transaction bodies are pure with respect to their snapshot,
    then
        Parallel(P, J) = Seq(P, J).

  Model notes (faithful to m0.py / state_of_project.md):

  * BODY LANGUAGE ENRICHED vs Lemma1.lean: bodies now contain `ite`
    (conditionals), restoring fidelity to m0.py, where branch
    conditions participate in validation.  This was flagged by the
    owner as the point where "Lean may resist": validation must cover
    CONTROL FLOW, not only data flow.  In this model it does, by
    construction: expressions read only locals, locals are populated
    only by `read` operations, and every snapshot read is recorded in
    the read-set.  Hence a branch condition is a function of recorded
    observations, and read-set agreement pins down the control path
    (see `runInstr_snapshot_adequate`, case `ite`).  Nothing extra to
    assume — it falls out of the closed term structure.
    All Lemma-1 results are RE-PROVED below for the enriched language
    (§0), so this file is self-contained and strictly supersedes the
    straight-line model; Lemma1.lean remains as the historical
    artifact.  Post-branch code is written inside the arms (A-normal
    style); this loses no expressiveness for finite bodies.

  * READ-YOUR-WRITES is separated from snapshot observation: a read
    satisfied by the local write buffer does NOT enter the read-set
    (lookup = local write, else snapshot — exactly m0.py's Ctx.read).
    The read-set is the set of external dependencies, not an
    execution trace.

  * PURITY (premise 3) is not an assumption but a fact of the term
    language: `runInstr` is a total function of (σ, body); the closed
    AST offers nothing ambient to observe.  This is Attack K's
    semantic-closure point, now load-bearing inside the proof.

  * THE PARALLEL MACHINE (§3).  Configuration = (committed state,
    committed output, remaining journal).  One rule:
      COMMIT: only the journal head may commit (premise 1); the
      snapshot σ of the committing attempt is chosen by an
      UNRESTRICTED ADVERSARY — σ need not be any historical committed
      state.  This subsumes every interleaving of START/EVAL/ABORT
      steps and all speculation.  Validation of the read-set gates
      the rule (premise 2).
    START/EVAL/ABORT steps do not change the configuration (an
    aborted attempt is dropped), so a `Par` trace is the commit
    skeleton of any machine run.

  * SAFETY vs PROGRESS are separated, as instructed:
      - `par_refines_seq` (safety): every committed prefix is the Seq
        prefix — UNCONDITIONAL, holds under any adversarial schedule,
        even one that never completes.
      - `par_progress` (existence): the machine CAN always complete —
        an attempt evaluated on the current committed state validates
        trivially.  Turning "can" into "will" needs weak fairness of
        the real scheduler (eventually START/COMMIT for the journal
        head fire); that is an assumption about the machine, not the
        semantics, and is deliberately NOT formalized here.
    X is about the correctness of results; liveness is a property of
    implementations.

  Proof skeleton (induction over logical time, invariant
  "committed prefix = Seq prefix"):
    runInstr_rs_mono            read-set only grows
    runInstr_snapshot_adequate  read-set agreement ⇒ identical run
                                (data AND control flow)
    runInstr_realizes_runBody   run against committed state = the
                                reference body step (S ⊕ ω)
    commit_step / commit_evalBody   valid commit = exact Seq step
    par_refines_seq             safety: Parallel(P,J) ⊆ Seq(P,J)
    par_progress                existence via fresh snapshots
    lemma2_commit_order         headline: Parallel(P,J) = Seq(P,J)
-/

/- ================================================================
   §0  The M₀ body language (enriched with `ite`) and its
       sequential semantics; Lemma-1 results re-proved.
   ================================================================ -/

abbrev Cell : Type := String
abbrev Var  : Type := String
abbrev State : Type := Cell → Int
abbrev Env   : Type := Var → Int
abbrev Out   : Type := List Int

/-- Expressions read LOCALS ONLY — cells are reachable exclusively via
    the `read` operation, which is what makes the read-set a complete
    account of external dependencies (including branch conditions). -/
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

/-- Transaction bodies: straight-line ops + conditionals.
    Convention: `ite e b₁ b₂` runs `b₁` iff `evalExpr ρ e ≠ 0`. -/
inductive Body where
  | done  : Body
  | read  : Cell → Var → Body → Body    -- x := cell; continue
  | write : Cell → Expr → Body → Body   -- cell := e; continue
  | emit  : Expr → Body → Body          -- output e; continue
  | ite   : Expr → Body → Body → Body   -- branch on a local expression

def updEnv (ρ : Env) (x : Var) (n : Int) : Env :=
  fun y => if y = x then n else ρ y

def updState (s : State) (c : Cell) (n : Int) : State :=
  fun d => if d = c then n else s d

/-- Reference big-step evaluation of a body (read-your-writes via the
    working state, `emit` the only output channel). -/
inductive EvalBody :
    State → Env → Out → Body → State → Out → Prop where
  | done : EvalBody s ρ o .done s o
  | read :
      EvalBody s (updEnv ρ x (s c)) o k s' o' →
      EvalBody s ρ o (.read c x k) s' o'
  | write :
      EvalBody (updState s c (evalExpr ρ e)) ρ o k s' o' →
      EvalBody s ρ o (.write c e k) s' o'
  | emit :
      EvalBody s ρ (o ++ [evalExpr ρ e]) k s' o' →
      EvalBody s ρ o (.emit e k) s' o'
  | iteTrue :
      evalExpr ρ e ≠ 0 →
      EvalBody s ρ o b₁ s' o' →
      EvalBody s ρ o (.ite e b₁ b₂) s' o'
  | iteFalse :
      evalExpr ρ e = 0 →
      EvalBody s ρ o b₂ s' o' →
      EvalBody s ρ o (.ite e b₁ b₂) s' o'

abbrev TxId := Nat
abbrev Program := TxId → Body
abbrev Journal := List TxId

def ρ₀ : Env := fun _ => 0

/-- Reference semantics: sequential fold of the journal. -/
inductive EvalSeq :
    Program → State → Out → Journal → State → Out → Prop where
  | nil  : EvalSeq P s o [] s o
  | cons :
      EvalBody s ρ₀ o (P t) s' o' →
      EvalSeq P s' o' J s'' o'' →
      EvalSeq P s o (t :: J) s'' o''

/-- Determinism of body evaluation (Lemma-1 machinery, enriched AST). -/
theorem evalBody_det
    (h₁ : EvalBody s ρ o b s₁ o₁) (h₂ : EvalBody s ρ o b s₂ o₂) :
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

/-- **Lemma 1 (Deterministic fold), enriched AST.** -/
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

/-- Executable reference body step. -/
def runBody : State → Env → Out → Body → State × Out
  | s, _, o, .done => (s, o)
  | s, ρ, o, .read c x k  => runBody s (updEnv ρ x (s c)) o k
  | s, ρ, o, .write c e k => runBody (updState s c (evalExpr ρ e)) ρ o k
  | s, ρ, o, .emit e k    => runBody s ρ (o ++ [evalExpr ρ e]) k
  | s, ρ, o, .ite e b₁ b₂ =>
      if evalExpr ρ e = 0 then runBody s ρ o b₂ else runBody s ρ o b₁

/-- Executable reference fold. -/
def runSeq (P : Program) : State → Out → Journal → State × Out
  | s, o, [] => (s, o)
  | s, o, t :: J =>
      let r := runBody s ρ₀ o (P t)
      runSeq P r.1 r.2 J

theorem runBody_sound :
    ∀ b s ρ o, EvalBody s ρ o b (runBody s ρ o b).1 (runBody s ρ o b).2 := by
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

theorem runSeq_sound :
    ∀ J P s o, EvalSeq P s o J (runSeq P s o J).1 (runSeq P s o J).2 := by
  intro J
  induction J with
  | nil => intro P s o; exact .nil
  | cons t J ih =>
      intro P s o
      exact .cons (runBody_sound ..) (ih ..)

/-- **Corollary (Lemma 1).** Seq(P,J) has exactly one result. -/
theorem seq_unique_result (P : Program) (J : Journal) (s : State) :
    ∃ r : State × Out, EvalSeq P s [] J r.1 r.2 ∧
      ∀ r' : State × Out, EvalSeq P s [] J r'.1 r'.2 → r' = r := by
  refine ⟨runSeq P s [] J, runSeq_sound .., ?_⟩
  intro r hr
  obtain ⟨hs, ho⟩ := lemma1_seq_deterministic hr (runSeq_sound ..)
  exact Prod.ext hs ho

/- ================================================================
   §1  Instrumented semantics: snapshot + write buffer + read-set
   ================================================================ -/

/-- Local write buffer of a running transaction (read-your-writes). -/
abbrev Writes : Type := Cell → Option Int

/-- Read-set: every (cell, value) the body observed FROM THE SNAPSHOT.
    Reads satisfied by the local write buffer are not snapshot
    observations and are not recorded (external dependencies, not an
    execution trace). -/
abbrev ReadSet : Type := List (Cell × Int)

def updW (w : Writes) (c : Cell) (n : Int) : Writes :=
  fun d => if d = c then some n else w d

/-- Commit action `S ⊕ ω`: apply a write buffer on a base state. -/
def applyW (S : State) (w : Writes) : State :=
  fun c => (w c).getD (S c)

/-- Empty write buffer. -/
def w₀ : Writes := fun _ => none

/-- Instrumented evaluation against a FIXED snapshot σ.
    Purity is structural: a total function of (σ, body). -/
def runInstr (σ : State) : Writes → Env → Out → ReadSet → Body → Writes × Out × ReadSet
  | w, _, o, rs, .done => (w, o, rs)
  | w, ρ, o, rs, .read c x k =>
      match w c with
      | some v => runInstr σ w (updEnv ρ x v) o rs k
      | none   => runInstr σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k
  | w, ρ, o, rs, .write c e k => runInstr σ (updW w c (evalExpr ρ e)) ρ o rs k
  | w, ρ, o, rs, .emit e k    => runInstr σ w ρ (o ++ [evalExpr ρ e]) rs k
  | w, ρ, o, rs, .ite e b₁ b₂ =>
      if evalExpr ρ e = 0 then runInstr σ w ρ o rs b₂ else runInstr σ w ρ o rs b₁

/-- One transaction attempt: run the body on snapshot σ from scratch. -/
def runTx (σ : State) (b : Body) : Writes × Out × ReadSet :=
  runInstr σ w₀ ρ₀ [] [] b

/-- Snapshot validation against the committed state S (premise 2). -/
def validates (S : State) (rs : ReadSet) : Prop := ∀ p ∈ rs, S p.1 = p.2

/-- The read-set accumulator only grows. -/
theorem runInstr_rs_mono :
    ∀ b σ w ρ o rs p, p ∈ rs → p ∈ (runInstr σ w ρ o rs b).2.2 := by
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

/-- Every read-set entry was either present already or records the
    snapshot's own value at that cell. -/
theorem runInstr_rs_from_snapshot :
    ∀ b σ w ρ o rs p, p ∈ (runInstr σ w ρ o rs b).2.2 → p ∈ rs ∨ σ p.1 = p.2 := by
  intro b
  induction b with
  | done => intro σ w ρ o rs p hp; exact .inl (by simpa [runInstr] using hp)
  | read c x k ih =>
      intro σ w ρ o rs p hp
      cases hw : w c with
      | some v => exact ih σ w (updEnv ρ x v) o rs p (by simpa [runInstr, hw] using hp)
      | none   =>
          have hp' : p ∈ (runInstr σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k).2.2 := by
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

/- ================================================================
   §2  Snapshot adequacy and realization
   ================================================================ -/

/-- **Snapshot adequacy.** If a state S agrees with snapshot σ on every
    observation of the σ-run (its read-set validates against S), the
    run against S is IDENTICAL — same writes, same output, same
    read-set, and (case `ite`) the same control path: the branch
    condition is a function of locals, locals come only from recorded
    reads, so read-set agreement pins the condition's value.  This is
    the formal content of "validation covers control flow". -/
theorem runInstr_snapshot_adequate :
    ∀ b σ S w ρ o rs,
      (∀ p ∈ (runInstr σ w ρ o rs b).2.2, S p.1 = p.2) →
      runInstr S w ρ o rs b = runInstr σ w ρ o rs b := by
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
          have hmem : (c, σ c) ∈ (runInstr σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) k).2.2 :=
            runInstr_rs_mono k σ w (updEnv ρ x (σ c)) o (rs ++ [(c, σ c)]) (c, σ c)
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

theorem applyW_updW (S : State) (w : Writes) (c : Cell) (n : Int) :
    applyW S (updW w c n) = updState (applyW S w) c n := by
  funext d
  by_cases hd : d = c <;> simp [applyW, updW, updState, hd]

theorem applyW_empty (S : State) : applyW S w₀ = S := by
  funext c; simp [applyW, w₀]

/-- **Realization.** The instrumented run against the committed state S
    computes exactly the reference body step: final state = S ⊕ ω,
    same output. -/
theorem runInstr_realizes_runBody :
    ∀ b S w ρ o rs,
      runBody (applyW S w) ρ o b
        = (applyW S (runInstr S w ρ o rs b).1, (runInstr S w ρ o rs b).2.1) := by
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

/-- Output accumulator shift for the reference semantics. -/
theorem runBody_out_shift :
    ∀ b s ρ o, runBody s ρ o b = ((runBody s ρ [] b).1, o ++ (runBody s ρ [] b).2) := by
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

/-- **Commit step.** If an attempt evaluated on an ARBITRARY snapshot σ
    validates against the committed state S, committing its effects
    performs exactly the reference Seq step from S. -/
theorem commit_step (S : State) (b : Body) (o : Out) (σ : State)
    (hval : validates S (runTx σ b).2.2) :
    runBody S ρ₀ o b = (applyW S (runTx σ b).1, o ++ (runTx σ b).2.1) := by
  have hadq : runInstr S w₀ ρ₀ [] [] b = runInstr σ w₀ ρ₀ [] [] b :=
    runInstr_snapshot_adequate b σ S w₀ ρ₀ [] [] (fun p hp => hval p hp)
  have hreal := runInstr_realizes_runBody b S w₀ ρ₀ [] []
  rw [applyW_empty] at hreal
  have hrefS : runBody S ρ₀ [] b = (applyW S (runTx σ b).1, (runTx σ b).2.1) := by
    unfold runTx
    rw [← hadq]
    exact hreal
  rw [runBody_out_shift b S ρ₀ o, hrefS]

/-- A validated commit performs a reference `EvalBody` step. -/
theorem commit_evalBody (S : State) (b : Body) (o : Out) (σ : State)
    (hval : validates S (runTx σ b).2.2) :
    EvalBody S ρ₀ o b (applyW S (runTx σ b).1) (o ++ (runTx σ b).2.1) := by
  have hb := runBody_sound b S ρ₀ o
  rw [commit_step S b o σ hval] at hb
  exact hb

/- ================================================================
   §3  The parallel machine and the theorem
   ================================================================ -/

/-- The parallel machine, as the commit skeleton of any run:
    * commits strictly in journal order (only the head commits) — (1);
    * σ chosen by an unrestricted adversary (subsumes every
      interleaving and any speculation; σ need not be a historical
      state) — the schedule, maximally strengthened;
    * read-set validation gates the commit — (2);
    * purity of bodies (3) is a fact of the closed term language.
    START/EVAL/ABORT steps do not change (committed state, committed
    output, remaining journal) and are therefore invisible here. -/
inductive Par (P : Program) : State → Out → Journal → State → Out → Prop where
  | nil : Par P s o [] s o
  | commit (σ : State) :
      validates s (runTx σ (P t)).2.2 →
      Par P (applyW s (runTx σ (P t)).1) (o ++ (runTx σ (P t)).2.1) J s' o' →
      Par P s o (t :: J) s' o'

/-- **Safety half of Lemma 2 (unconditional).** Every parallel
    execution — under any adversarial schedule, complete or not as a
    machine run — realizes exactly the sequential semantics on the
    journal it commits.  Induction over logical time with invariant
    "committed prefix = Seq prefix". -/
theorem par_refines_seq
    (h : Par P s o J s' o') : EvalSeq P s o J s' o' := by
  induction h with
  | nil => exact .nil
  | commit σ hval _ ih => exact .cons (commit_evalBody _ _ _ σ hval) ih

/-- **Existence half.** The machine CAN always drive the journal to
    completion: an attempt evaluated on the current committed state
    validates trivially, and this strategy reproduces the executable
    fold `runSeq`.  (Whether the machine WILL do so is weak fairness
    of the scheduler — an implementation property, not part of X.) -/
theorem par_progress :
    ∀ J P s o, Par P s o J (runSeq P s o J).1 (runSeq P s o J).2 := by
  intro J
  induction J with
  | nil => intro P s o; exact Par.nil
  | cons t J ih =>
      intro P s o
      have hval : validates s (runTx s (P t)).2.2 := by
        intro p hp
        rcases runInstr_rs_from_snapshot (P t) s w₀ ρ₀ [] [] p hp with h | h
        · cases h
        · exact h
      refine Par.commit s hval ?_
      have hstep := commit_step s (P t) o s hval
      have hfold : runSeq P s o (t :: J)
          = runSeq P (applyW s (runTx s (P t)).1) (o ++ (runTx s (P t)).2.1) J := by
        simp only [runSeq, hstep]
      rw [hfold]
      exact ih P (applyW s (runTx s (P t)).1) (o ++ (runTx s (P t)).2.1)

/-- **Lemma 2 (Commit-order theorem).**  For every program P, journal J
    and initial state:
    (1) a completed parallel execution exists, and
    (2) EVERY parallel execution — any adversarial schedule, any
        speculative snapshots — ends in the same (State, Out), which
        is exactly Seq(P, J), the unique result of Lemma 1.
    In the project's notation: Parallel(P, J) = Seq(P, J).
    Determinism is thus not a property of a scheduler: any scheduler
    is correct provided validation + ordered commit — a theorem about
    the class of implementations. -/
theorem lemma2_commit_order (P : Program) (J : Journal) (s : State) :
    Par P s [] J (runSeq P s [] J).1 (runSeq P s [] J).2 ∧
    ∀ s' o', Par P s [] J s' o' → (s', o') = runSeq P s [] J := by
  refine ⟨par_progress J P s [], ?_⟩
  intro s' o' h
  obtain ⟨hs, ho⟩ :=
    lemma1_seq_deterministic (par_refines_seq h) (runSeq_sound J P s [])
  exact Prod.ext hs ho
