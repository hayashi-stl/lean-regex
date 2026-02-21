import Regex.Algorithm.Defs
import Regex.Algorithm.StackDMO
import Regex.Except

-- A general termination argument based on decreasing actions

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace MatchStack

def stepN (n : ℕ) (st : MatchStack w) : StepResult w
  := match n with
  | 0 => Except.ok st
  | n + 1 => st.step >>= stepN n

@[simp] theorem step0_eq_self : stepN (w := w) 0 = Except.ok := by rfl

@[simp] theorem step1_eq_step : stepN (w := w) 1 = step := by
  ext; rw [stepN, step0_eq_self, Except.ok_eq_pure, bind_pure]

theorem stepN_step_eq_step_stepN {st : MatchStack w} {n : ℕ}
    : st.stepN n >>= step = st.step >>= stepN n:= by
  induction n generalizing st with
  | zero =>
    simp only [step0_eq_self, Except.ok_eq_pure, bind_pure, pure_bind]
  | succ n ind =>
    simp only [stepN, bind_assoc]
    congr; ext x; exact ind

theorem stepN_of_stepN_add_one {st : MatchStack w} {n : ℕ} {st'' : MatchStack w}
    (hst : st.stepN (n + 1) = Except.ok st'')
    : ∃ st', st.stepN n = Except.ok st' := by
  by_contra!
  obtain ⟨mat, eq⟩ := Except.eq_error_iff_forall_ne_ok.mp this
  rw [stepN, ← stepN_step_eq_step_stepN, eq] at hst
  obtain eq' := Except.error_bind mat step
  simp [eq'] at hst

theorem stepN_step_of_stepN_add_one {st : MatchStack w} {n : ℕ} {st'' : MatchStack w}
    (hst : st.stepN (n + 1) = Except.ok st'')
    : ∃ st', st.stepN n = Except.ok st' ∧ st'.step = Except.ok st'' := by
  have ⟨st', hst'⟩ := stepN_of_stepN_add_one hst
  use st', hst'
  rw [stepN, ← stepN_step_eq_step_stepN, hst', Except.ok_bind] at hst
  rwa [Except.ok_eq_pure]

theorem stepN_add {st : MatchStack w} {m n : ℕ} {st'' : MatchStack w}
    (hst : st.stepN (m + n) = Except.ok st'')
    : ∃ st', st.stepN m = Except.ok st' ∧ st'.stepN n = Except.ok st'' := by
  induction n generalizing st st'' with
  | zero =>
    rw [add_zero] at hst
    conv in _ ∧ _ => rw [step0_eq_self, Except.ok.injEq]
    use st''
  | succ n ind =>
    rw [← add_assoc] at hst
    obtain ⟨st', hst', st'eq⟩ := stepN_step_of_stepN_add_one hst
    obtain ⟨st'_, hst'_, st'_eq⟩ := ind hst'
    use st'_, hst'_
    rwa [stepN, ← stepN_step_eq_step_stepN, st'_eq]

theorem stepN_add_eq_bind {st : MatchStack w} {m n : ℕ}
    : st.stepN (m + n) = st.stepN m >>= stepN n := by
  induction m generalizing st with
  | zero => simp
  | succ m ind => rw [Nat.add_right_comm, stepN, stepN, bind_assoc]; simp [← ind]

theorem step_stepN_of_stepN_add_one {st : MatchStack w} {n : ℕ} {st'' : MatchStack w}
    (hst : st.stepN (n + 1) = Except.ok st'')
    : ∃ st', st.step = Except.ok st' ∧ st'.stepN n = Except.ok st'' := by
  have add := stepN_add (add_comm n 1 ▸ hst); simp only [step1_eq_step] at add; exact add

theorem stepN_step {st : MatchStack w} {n : ℕ} {st' : MatchStack w}
    (hst : st.stepN n = Except.ok st') : st.stepN (n + 1) = st'.step := by
  rw [stepN, ← stepN_step_eq_step_stepN, hst, Except.ok_bind]

/-- A stack terminates if it runs for a finite number of steps -/
def Terminates (st : MatchStack w) :=
  Acc (fun st'' st' : MatchStack w ↦ st'.step = Except.ok st'') st

/-- The termination condition lifted to `StepResult` -/
def Terminates' (st : StepResult w) :=
  match st with | Except.ok st => st.Terminates | Except.error _ => True

theorem terminates_of_stepN {st : MatchStack w} {n : ℕ} {mat : PartialMatches w}
    (hst : st.stepN n = Except.error mat) : st.Terminates := by
  cases n with | zero => simp at hst | succ n => induction n generalizing st mat with
  | zero =>
    rw [zero_add, step1_eq_step] at hst
    apply Acc.intro
    intro st' eq
    simp [hst] at eq
  | succ n ind =>
    cases h : st.stepN (n + 1) with
    | ok st'' =>
      rw [add_comm] at h
      have ⟨st', hst', st'eq⟩ := stepN_add h
      rw [step1_eq_step] at hst'
      rw [stepN, hst', Except.ok_bind] at hst
      specialize ind hst
      exact Acc.intro st fun st'_ hst'_ ↦ by
        rw [hst', Except.ok.injEq] at hst'_; exact hst'_ ▸ ind
    | error mat' => exact ind h

theorem terminates_iff {st : MatchStack w}
    : st.Terminates ↔ ∃ n mat, st.stepN n = Except.error mat := by
  constructor
  · intro term
    induction term with
    | intro st hst ind =>
      cases h : st.step with
      | ok st' =>
        obtain ⟨n, mat, stepn⟩ := ind st' h
        use n + 1, mat
        rwa [stepN, h, Except.ok_bind]
      | error mat => use 1, mat; rwa [step1_eq_step]
  · simp only [forall_exists_index]
    exact fun n mat ↦ terminates_of_stepN

theorem step_terminates {st st' : MatchStack w} (term : st.Terminates)
    (hst : st.step = Except.ok st') : st'.Terminates := Acc.inv term hst

theorem stepN_terminates {st st' : MatchStack w} (term : st.Terminates) {n : ℕ}
    (hst : st.stepN n = Except.ok st') : st'.Terminates := by
  have ⟨n', mat, stepn⟩ := terminates_iff.mp term
  have lt : n < n' := by
    by_contra!
    rw [← Nat.add_sub_cancel' this, stepN_add_eq_bind, stepn] at hst
    simp at hst
  rw [← Nat.add_sub_cancel' (le_of_lt lt), stepN_add_eq_bind, hst,
    Except.ok_bind] at stepn
  exact terminates_of_stepN stepn

/-- A stack terminates iff it still terminates when stepped. -/
theorem step_terminates_iff {st : MatchStack w}
    : st.Terminates ↔ Terminates' st.step := by
  rw [Terminates'.eq_def]
  split <;> expose_names
  · constructor
    · exact fun term ↦ step_terminates term heq
    · rw [terminates_iff, terminates_iff]
      rintro ⟨n, mat, stepn⟩
      use (n + 1), mat
      rwa [stepN, heq, Except.ok_bind]
  · constructor <;> simp only [implies_true, forall_const]
    rw [terminates_iff]; use 1, a; simpa

theorem pop_top {st : MatchStack w} {as bs : List (Action w)}
    (term : (mk as st.arg).Terminates) (hst : st.entries = as ++ bs)
    : ∃ n st'', st.stepN n = Except.ok st'' ∧ st''.entries = bs ∧
      ∀ n' < n, ∀ st', st.stepN n' = Except.ok st' →
        ∃ ac as', st'.entries = ac :: as' ++ bs := by
  obtain ⟨n, mat, err⟩ := terminates_iff.mp term
  induction n generalizing st as with
  | zero => simp at err
  | succ n ind =>
    rw [stepN] at err
    cases h : st.step with -- oops, cased here out of habit
    | ok st' =>
      rw [step_terminates_iff, Terminates'.eq_def] at term
      split at term
      case h_1 ast' hast' =>
        cases has : as with
        | nil => rw [has, List.nil_append] at hst; use 0, st; simpa
        | cons a_ as_ =>
          obtain ⟨aac, aas', haac, ast'eq⟩ := step_eq_ok hast'
          obtain ⟨ac, as', hac, st'eq⟩ := step_eq_ok h
          simp only at ast'eq haac
          simp only [hst, has, List.cons_append, List.cons.injEq] at hac
          simp only [has, List.cons.injEq] at haac
          simp only [List.cons_append, ← haac, ← hac, and_self] at *
          rw [← List.append_assoc, MatchStack.ext_iff] at st'eq
          simp only at st'eq
          rw [hast', Except.ok_bind] at err
          have ⟨n', st'', stepn', hst'', min⟩ := ind (st := st')
            (st'eq.2 ▸ ast'eq ▸ term) st'eq.1 (st'eq.2 ▸ ast'eq ▸ err)
          use n' + 1, st''
          rw [stepN, h, Except.ok_bind]
          refine ⟨stepn', hst'', ?_⟩
          intro n_ n_lt st_ hst_
          cases n_ with
          | zero =>
            rw [step0_eq_self, Except.ok_inj] at hst_
            use a_, as_; simp [← hst_, hst, has]
          | succ n_ =>
            rw [stepN, h, Except.ok_bind] at hst_
            exact min n_ (Nat.add_lt_add_iff_right.mp n_lt) st_ hst_
      case h_2 ast' hast' =>
        have hast' := step_eq_error hast'; simp at hast'
        use 0, st; simp [hst, hast']
    | error mat' =>
      have emp := step_eq_error h
      simp only [emp, List.nil_eq, List.append_eq_nil_iff] at hst
      use 0, st; simp [*]

theorem top_equiv {st : MatchStack w} {as bs : List (Action w)}
    (term : (mk as st.arg).Terminates) (hst : st.entries = as ++ bs)
    : ∃ n st'', st.stepN n = Except.ok st'' ∧ st''.entries = bs ∧
      (mk as st.arg).stepN (n + 1) = Except.error st''.arg := by
  have ⟨n, st'', stepn, st''eq, min⟩ := st.pop_top term hst
  induction n generalizing st as with
  | zero =>
    use 0, st'', stepn, st''eq
    rw [step0_eq_self, Except.ok_inj] at stepn
    simp only [stepn, st''eq, List.self_eq_append_left] at hst
    simp [hst, step, stepn]
  | succ n ind =>
    obtain ⟨st', hst_, hst'⟩ := st.step_stepN_of_stepN_add_one stepn
    obtain ⟨ac, as', hac, st'eq⟩ := st.step_eq_ok hst_
    cases as with
    | nil =>
      use 0, st, (by simp), (by simp [hst]); simp [step]
    | cons ac'' as'' =>
      simp only [hst, List.cons_append, List.cons.injEq] at hac
      have st'ent : st'.entries = (ac.process st.arg).entries ++ as'' ++ bs := by
        simp [st'eq, hac]
      simp only [Order.lt_add_one_iff, ← hac.2, hac.1, and_self, ← List.append_assoc] at *
      rw [step_terminates_iff, Terminates'.eq_def, step] at term
      simp only at term
      simp only [MatchStack.ext_iff] at st'eq
      specialize ind (st := st') (st'eq.2 ▸ term) st'ent hst' _
      · intro n' n'lt st'_ hst'_
        specialize min (n' + 1) (Nat.le_of_lt_add_one (Nat.add_lt_add_right n'lt 1)) st'_
        rw [stepN, hst_, Except.ok_bind] at min
        exact min hst'_
      have ⟨n, st'', hst', st''eq, starg⟩ := ind
      use n + 1, st''
      rw [stepN, hst_, Except.ok_bind]
      use hst', st''eq
      rw [stepN, step, Except.ok_bind]
      simpa only [show (ac.process st.arg).arg = st'.arg by simp [st'eq]]

--theorem pop_top {st : MatchStack w} {as bs : List (Action w)}
--    (term : st.Terminates) (hst : st.entries = as ++ bs)
--    : ∃ n st'', st.stepN n = Except.ok st'' ∧ st''.entries = bs ∧
--      ∀ n' < n, ∀ st', st.stepN n' = Except.ok st' →
--        ∃ ac as', st'.entries = ac :: as' ++ bs := by
--  obtain ⟨n, mat, err⟩ := st.terminates_iff.mp term
--  induction n generalizing st as with
--  | zero => simp at err
--  | succ n ind =>
--    rw [stepN] at err
--    cases h : st.step with -- oops, cased here out of habit
--    | ok st' =>
--      rw [h, Except.ok_bind] at err
--      obtain ⟨ac, as', hac, st'eq⟩ := st.step_eq_ok h
--      cases has : as with
--      | nil => rw [has, List.nil_append] at hst; use 0, st; simpa
--      | cons a_ as_ =>
--        simp only [hst, has, List.cons_append, List.cons.injEq] at hac
--        have ent : st'.entries = ?_ := by
--          simp only [st'eq, ← hac.2, ← List.append_assoc]; rfl
--        obtain ⟨n', st'', stepn', hst'', min⟩ := ind (st.step_terminates term h) ent err
--        use n' + 1, st''
--        rw [stepN, h, Except.ok_bind]
--        refine ⟨stepn', hst'', ?_⟩
--        intro n_ n_lt st_ hst_
--        cases n_ with
--        | zero =>
--          rw [step0_eq_self, Except.ok_inj] at hst_
--          use a_, as_; simpa [← hst_, ← has]
--        | succ n_ =>
--          rw [stepN, h, Except.ok_bind] at hst_
--          exact min n_ (Nat.add_lt_add_iff_right.mp n_lt) st_ hst_
--    | error mat' =>
--      have emp := step_eq_error h
--      simp only [emp, List.nil_eq, List.append_eq_nil_iff] at hst
--      use 0, st; simp [*]

/-- An older version of `top_equiv` that assumes `st.Terminates` instead -/
theorem top_equiv {st : MatchStack w} (term : st.Terminates)
    {as bs : List (Action w)} (hst : st.entries = as ++ bs)
    : ∃ n st'', st.stepN n = Except.ok st'' ∧ st''.entries = bs ∧
      (mk as st.arg).stepN (n + 1) = Except.error st''.arg := by
  have ⟨n, st'', stepn, st''eq, min⟩ := st.pop_top term hst
  induction n generalizing st as with
  | zero =>
    use 0, st'', stepn, st''eq
    rw [step0_eq_self, Except.ok_inj] at stepn
    simp only [stepn, st''eq, List.self_eq_append_left] at hst
    simp [hst, step, stepn]
  | succ n ind =>
    obtain ⟨st', hst_, hst'⟩ := st.step_stepN_of_stepN_add_one stepn
    obtain ⟨ac, as', hac, st'eq⟩ := st.step_eq_ok hst_
    cases as with
    | nil =>
      use 0, st, (by simp), (by simp [hst]); simp [step]
    | cons ac'' as'' =>
      simp only [hst, List.cons_append, List.cons.injEq] at hac
      have st'ent : st'.entries = (ac.process st.arg).entries ++ as'' ++ bs := by
        simp [st'eq, hac]
      specialize ind (st.step_terminates term hst_) st'ent hst' _
      · intro n' n'lt st'_ hst'_
        specialize min (n' + 1) (Nat.add_lt_add_right n'lt 1) st'_
        rw [stepN, hst_, Except.ok_bind] at min
        exact min hst'_
      have ⟨n, st'', hst', st''eq, starg⟩ := ind
      use n + 1, st''
      rw [stepN, hst_, Except.ok_bind, hac.1]
      use hst', st''eq
      rw [stepN, step, Except.ok_bind]
      simpa only [show (ac.process st.arg).arg = st'.arg by simp [st'eq]]


theorem top_terminates {st : MatchStack w} {as bs : List (Action w)}
    (term : st.Terminates) (hst : st.entries = as ++ bs)
    : (mk as st.arg).Terminates := by
  have ⟨n, mat, stepn⟩ := terminates_iff.mp term
  induction n generalizing st as with
  | zero => simp at stepn
  | succ n ind =>

  have ⟨_, _, _, _, err⟩ := st.top_equiv term hst
  exact terminates_of_stepN err

structure Terminator (w : List α) where
  /-- The condition -/
  toFun : MatchStack w → Prop
  /-- The condition ensures termination -/
  term : ∀ st, toFun st → st.Terminates
  /-- The condition is preserved -/
  pres : ∀ st st', toFun st → st.step = Except.ok st' → toFun st'

instance : FunLike (Terminator w) (MatchStack w) Prop where
  coe := Terminator.toFun
  coe_injective' f g h := by cases f; cases g; congr

def Terminates.terminator : Terminator w where
  toFun st := st.Terminates
  term _ fst := fst
  pres _ _ fst steq := Acc.inv fst steq

--/-- The subtype of stacks satisfying a particular termination condition.
--The condition must be preserved. -/
--def T' (f : Terminator w)
--  := {st : MatchStack w // f st}

/-- The subtype of all terminating stacks -/
@[reducible] def T (w : List α) := {st : MatchStack w // st.Terminates}

end MatchStack

variable {f : MatchStack.Terminator w}

namespace Action

def matchStackT (ac : Action w) (arg : PartialMatches w)
    (term : (ac.matchStack arg).Terminates)
    : MatchStack.T w :=
  ⟨ac.matchStack arg, term⟩

end Action

namespace MatchStack

namespace T

def StepResult (w : List α) :=
  Except (PartialMatches w) (MatchStack.T w)

instance instWellFoundedRelation : WellFoundedRelation (MatchStack.T w) := Acc.wfRel

def step (st : MatchStack.T w) : StepResult w
  := match h : st.val.step with
  | Except.ok st' => Except.ok ⟨st', Acc.inv st.prop h⟩
  | Except.error result => Except.error result

theorem step_coe {st : MatchStack.T w} : Subtype.val <$> st.step = st.val.step := by
  simp only [step]
  split <;> (
    expose_names;
    simp only [Except.map_ok, Except.map_error]
    exact Eq.symm heq)

theorem step_eq_ok_coe {st st' : MatchStack.T w}
    : st.step = Except.ok st' ↔ st.val.step = Except.ok st'.val := by
  have adv := st.step_coe
  constructor <;> intro eq
  · simp only [eq, Except.map_ok] at adv; exact Eq.symm adv
  · simp only [eq, ← Except.map_ok] at adv
    rw [map_inj_right Subtype.val_inj.mp] at adv
    exact adv

theorem step_eq_error_coe {st : MatchStack.T w} {res : PartialMatches w}
    : st.step = Except.error res ↔ st.val.step = Except.error res := by
  have adv := st.step_coe
  constructor <;> intro eq
  · simp only [eq, Except.map_error] at adv; exact Eq.symm adv
  · simp only [eq, ← Except.map_error] at adv
    rw [← Except.map_error Subtype.val, map_inj_right Subtype.val_inj.mp] at adv
    exact adv

theorem step_eq_ok {st st' : MatchStack.T w} (hst : st.step = Except.ok st')
    : ∃ (ac : Action w) (as : List (Action w)),
        st.val.entries = ac :: as ∧ st'.val = MatchStack.mk
          (entries := (ac.process st.val.arg).entries ++ as)
          (arg := (ac.process st.val.arg).arg)
  := st.val.step_eq_ok (step_eq_ok_coe.mp hst)

theorem step_singleton (ac : Action w) {arg : PartialMatches w}
    (term : (ac.matchStack arg).Terminates)
    : (ac.matchStackT arg term).step = Except.ok ⟨
        ac.process arg, Acc.inv term (step_singleton ac arg)
      ⟩ := by
  rw [step_eq_ok_coe, Action.matchStackT]
  exact MatchStack.step_singleton ac arg

/-- Run the matching algorithm to completion! -/
def run (st : MatchStack.T w) : PartialMatches w :=
  match _ : st.step with
  | Except.ok st' => st'.run
  | Except.error res => res
termination_by st
decreasing_by
  simpa [← step_eq_ok_coe]

end T

theorem coe_val {st : MatchStack w} (term : st.Terminates)
  : st = (⟨st, term⟩ : T w).val := rfl

theorem run_of_stepN {st : MatchStack w} {n : ℕ} {mat : PartialMatches w}
    (hst : st.stepN n = Except.error mat)
    : T.run ⟨st, terminates_of_stepN hst⟩ = mat := by
  have term := terminates_of_stepN hst
  induction n generalizing st with | zero => simp at hst | succ n ind =>
    cases h : st.step with
    | ok st' =>
      rw [stepN, h, Except.ok_bind] at hst
      specialize ind hst (st.step_terminates term h)
      rw [coe_val term, coe_val (st.step_terminates term h), ← T.step_eq_ok_coe] at h
      rw [T.run, h]
      simpa
    | error mat' =>
      rw [stepN, h, Except.error_bind, Except.error_inj] at hst
      rw [coe_val term, ← T.step_eq_error_coe] at h
      rw [T.run, h, hst]

theorem top_run_equiv {st : MatchStack w}
    {as bs : List (Action w)} (hst : st.entries = as ++ bs)
    (term : (mk as st.arg).Terminates)
    : ∃ n, st.stepN n =
      Except.ok (mk bs (T.run ⟨mk as st.arg, term⟩)) := by
  have ⟨n, st', hst', st'eq, stepn⟩ := st.top_equiv term hst
  use n
  have run := run_of_stepN stepn
  simp only [run, hst']
  rw [Except.ok_inj]
  have st'mk : st' = mk st'.entries st'.arg := rfl
  rwa [st'eq] at st'mk

--theorem top_run_terminates {st : MatchStack w} (term : st.Terminates)
--    {as bs : List (Action w)} (hst : st.entries = as ++ bs)
--    : (mk bs (T.run ⟨mk as st.arg, st.top_terminates term hst⟩)).Terminates := by
--  have ⟨n, top⟩ := st.top_run_equiv term hst
--  exact stepN_terminates term top

theorem top_run_terminates_iff {st : MatchStack w} {n : ℕ}
    {as bs : List (Action w)} (hst : st.entries = as ++ bs)
    : st.Terminates ↔ ∃ top : (mk as st.arg).Terminates,
      (mk bs (T.run ⟨mk as st.arg, top⟩)).Terminates := by
  constructor
  · intro term
    use st.top_terminates term hst
    have ⟨n, top⟩ := st.top_run_equiv term hst
    exact stepN_terminates term top
  · intro ⟨term, run⟩


def step_acc {β : Type*} {f : β → MatchStack w} {a : β}
    (acc : Acc (fun b a ↦ (f a).step = Except.ok (f b)) a)
    (emb : ∀ a st', (f a).step = Except.ok st' → ∃ b, f b = st')
    : (f a).Terminates := by
  induction acc with
  | intro a' acc' a'ind =>
    apply Acc.intro
    intro st' st'eq
    obtain ⟨b, fb⟩ := emb a' st' st'eq
    exact fb ▸ a'ind b (fb ▸ st'eq)

end MatchStack

namespace Action

/-- The first action can be stepped to from the second action -/
def InvStep (law : Action w → PartialMatches w → Prop) (ac' ac : Action w) :=
  ∃ arg, law ac arg ∧ ac' ∈ (ac.process arg).entries

/-- A law that actions must follow given an argument. -/
structure Law (w : List α) where
  /-- The law -/
  toFun : Action w → PartialMatches w → Prop
  /-- The law ensures termination -/
  term : ∀ ac arg, toFun ac arg →
    Acc (fun ac' ac ↦ InvStep toFun ac' ac) ac
  /-- The law is preserved when an argument is pushed -/
  push : ∀ ac arg, toFun ac arg →
    ∀ ac' as', (ac.process arg).entries = ac' :: as' → toFun ac' (ac.process arg).arg
      ∧ ∀ a ∈ as', ∃ arg, toFun a arg
  /-- The law is preserved when an argument is popped -/
  pop : ∀ ac arg, toFun ac arg →
    ∀ n ac1 ac2 as arg',
    (ac.matchStack arg).stepN n = Except.ok ⟨ac1 :: ac2 :: as, arg'⟩ →
    (ac1.process arg').entries = [] → toFun ac2 (ac1.process arg').arg

instance : FunLike (Law w) (Action w) (PartialMatches w → Prop) where
  coe := Law.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- The specific actions that are lawful and terminate based on `l` -/
def L (l : Law w) := {ac : Action w // ∃ arg, l ac arg}

namespace L

instance instWellFoundedRelation {l : Law w} : WellFoundedRelation (Action.L l) where
  rel ac' ac := InvStep l ac'.val ac.val
  wf := WellFounded.intro fun ac ↦
    InvImage.accessible (r := InvStep l) (fun ac : L l ↦ ac.val)
    (by obtain ⟨arg, law⟩ := ac.prop; exact l.term ac.val arg law)

end L

end Action

namespace MatchStack

open scoped StackDMO

/-- A state is reachable with some law if there is an action and argument
that satisfies the law and can reach this state -/
def Reachable (st : MatchStack w) (l : Action w → PartialMatches w → Prop) :=
  ∃ ac arg, l ac arg ∧ ∃ n, (ac.matchStack arg).stepN n = Except.ok st

theorem Reachable.step {l : Action.Law w} {st st' : MatchStack w} (reach : st.Reachable l)
    (hst : st.step = Except.ok st')
    : st'.Reachable l := by
  rcases reach with ⟨ac₀, arg₀, law, n, stepn⟩
  use ac₀, arg₀, law, n + 1
  exact hst ▸ stepN_step stepn

theorem law_arg_preserved {l : Action.Law w} {st : MatchStack w}
    (stepn : st.Reachable l)
    {ac : Action w} {as' : List (Action w)} (hac : st.entries = ac :: as')
    : l ac st.arg := by
  rcases stepn with ⟨ac₀, arg₀, law, n, stepn⟩
  induction n generalizing st ac as' with
  | zero =>
    rw [step0_eq_self, Except.ok.injEq, Action.matchStack] at stepn
    simp only [← stepn, List.cons.injEq, List.nil_eq] at hac ⊢
    rwa [← hac.1]
  | succ n ind =>
    obtain ⟨st_, stepn_, hst_⟩ := stepN_step_of_stepN_add_one stepn
    obtain ⟨ac_, as_, has_, hst⟩ := step_eq_ok hst_
    specialize ind has_ stepn_
    cases hac_ : (ac_.process st_.arg).entries with
    | nil =>
      rw [hac_, List.nil_append] at hst
      simp only [hst] at hac
      rw [show st_ = mk st_.entries st_.arg by rfl] at stepn_
      have pop := l.pop ac₀ arg₀ law n ac_ ac as' st_.arg (hac ▸ has_ ▸ stepn_)
        hac_
      simpa [hst]
    | cons a as =>
      have push := l.push ac_ st_.arg ind a as hac_
      simp only [hst, hac_, List.cons_append, List.cons.injEq] at hac
      obtain ⟨push, _⟩ := push
      simpa [← hac.1, hst]

theorem law_invStep {l : Action.Law w} {st st' : MatchStack w}
    : st.Reachable l →
    st.step = Except.ok st' → st'.entries ≺ˢ[Action.InvStep l] st.entries := by
  rintro ⟨ac₀, arg₀, law, n, stepn⟩ hst
  dsimp [(· ≺ˢ[·] ·)]
  cases n with
  | zero =>
    rw [step0_eq_self, Except.ok.injEq, Action.matchStack] at stepn
    simp only [← stepn, List.cons.injEq, List.nil_eq, exists_and_left, ↓existsAndEq,
      true_and, List.append_nil, exists_eq_left', Action.InvStep]
    obtain ⟨ac', as', has', hst'⟩ := step_eq_ok hst
    simp only [← stepn, List.cons.injEq, List.nil_eq, hst', List.mem_append] at has' ⊢
    simp only [← has'.1, has'.2, List.not_mem_nil, or_false]
    exact fun a mem ↦ ⟨arg₀, law, mem⟩
  | succ n =>
    obtain ⟨st_, stepn_, hst_⟩ := stepN_step_of_stepN_add_one stepn
    obtain ⟨ac', as', has', hst'⟩ := step_eq_ok hst
    simp only [hst', exists_and_left]
    simp only [Action.InvStep]
    use as', (ac'.process st.arg).entries, rfl, ac', has'
    intro a amem
    refine ⟨st.arg, ?_, amem⟩
    exact st.law_arg_preserved ⟨ac₀, arg₀, law, n + 1, stepn⟩ has'

theorem law_preserved {l : Action.Law w} {st : MatchStack w}
    : st.Reachable l →
    ∀ ac ∈ st.entries, ∃ arg, l ac arg := by
  rintro ⟨ac₀, arg₀, law, n, stepn⟩ ac mem
  induction n generalizing st ac with
  | zero =>
    rw [step0_eq_self, Except.ok.injEq, Action.matchStack] at stepn
    simp only [← stepn, List.mem_cons, List.not_mem_nil, or_false] at mem
    exact ⟨arg₀, mem ▸ law⟩
  | succ n ind =>
    obtain ⟨st_, stepn_, hst_⟩ := stepN_step_of_stepN_add_one stepn
    obtain ⟨ac_, as_, has_, hst⟩ := step_eq_ok hst_
    specialize ind stepn_
    simp only [has_, List.mem_cons, forall_eq_or_imp] at ind
    obtain ⟨⟨arg_, law_⟩, lawas_⟩ := ind
    cases h : (ac_.process st_.arg).entries with
    | nil =>
      simp only [hst, h, List.nil_append] at mem
      exact lawas_ ac mem
    | cons ac' as' =>
      have law_ := law_arg_preserved ⟨ac₀, arg₀, law, n, stepn_⟩ has_
      have push := l.push ac_ st_.arg law_ ac' as' h
      simp only [hst, h, List.cons_append, List.mem_cons, List.mem_append] at mem
      rcases mem with aceq | acmem | acmem
      · exact ⟨(ac_.process st_.arg).arg, aceq ▸ push.1⟩
      · exact push.2 ac acmem
      · exact lawas_ ac acmem

theorem law_action_acc {l : Action.Law w} {st : MatchStack w}
    : st.Reachable l →
    ∀ ac ∈ st.entries, Acc (Action.InvStep l) ac := by
  rintro reach ac mem
  obtain ⟨arg, law⟩ := st.law_preserved reach ac mem
  exact l.term ac arg law

/-- A terminator based on an action law.
Asserts that the stack is reachable by some lawful action and argument -/
def LawTerminator (l : Action.Law w) : Terminator w where
  toFun st := st.Reachable l
  --
  term st fst := by
    dsimp [Terminates]
    have wf := StackDMO.DMO.wf_raw (Action.InvStep l)
    cases wf; rename_i wf
    specialize wf st.entries
    have wf := InvImage.accessible entries wf
    induction wf with
    | intro st acc ind =>
      simp only [InvImage, and_imp] at *
      apply Acc.intro
      intro st' steq
      have wf' := Acc.inv wf ⟨law_invStep fst steq, law_action_acc fst⟩
      exact ind st' (law_invStep fst steq) (law_action_acc fst)
        (Reachable.step fst steq) wf'

  pres st st' fst steq := by
    rcases fst with ⟨ac, arg, law, n, stepn⟩
    use ac, arg, law, n + 1
    rwa [stepN_step stepn]

end MatchStack

end Regex
