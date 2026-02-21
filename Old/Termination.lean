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
  obtain ⟨mat', eq'⟩ := Except.error_bind_eq_error mat step
  simp [eq'] at hst

theorem stepN_step_of_stepN_add_one {st : MatchStack w} {n : ℕ} {st'' : MatchStack w}
    (hst : st.stepN (n + 1) = Except.ok st'')
    : ∃ st', st.stepN n = Except.ok st' ∧ st'.step = Except.ok st'' := by
  have ⟨st', hst'⟩ := stepN_of_stepN_add_one hst
  use st', hst'
  rw [stepN, ← stepN_step_eq_step_stepN, hst', Except.ok_eq_pure, pure_bind] at hst
  rwa [Except.ok_eq_pure]

theorem stepN_step {st : MatchStack w} {n : ℕ} {st' : MatchStack w}
    (hst : st.stepN n = Except.ok st') : st.stepN (n + 1) = st'.step := by
  rw [stepN, ← stepN_step_eq_step_stepN, hst, Except.ok_eq_pure, pure_bind]

/-- A stack terminates if it runs for a finite number of steps -/
def Terminates (st : MatchStack w) :=
  Acc (fun st'' st' : MatchStack w ↦ st'.step = Except.ok st'') st

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

/-- The subtype of stacks satisfying a particular termination condition.
The condition must be preserved. -/
def T' (f : Terminator w)
  := {st : MatchStack w // f st}

/-- The subtype of all terminating stacks -/
@[reducible] def T (w : List α) := T' (w := w) Terminates.terminator

end MatchStack

variable {f : MatchStack.Terminator w}

namespace Action

def matchStackT' (ac : Action w) (arg : PartialMatches w)
    (f : MatchStack.Terminator w) (fac : f (ac.matchStack arg))
    : MatchStack.T' f :=
  ⟨ac.matchStack arg, fac⟩

end Action

namespace MatchStack

namespace T'

def StepResult {w : List α} (f : Terminator w) :=
  Except (PartialMatches w) (MatchStack.T' f)

instance instWellFoundedRelation : WellFoundedRelation (MatchStack.T' f) where
  rel st' st := st.val.step = Except.ok st'.val
  wf := WellFounded.intro fun st ↦
    InvImage.accessible (fun st : T' f ↦ st.val)
    (f.term st.val st.prop)

def step (st : MatchStack.T' f) : StepResult f
  := match h : st.val.step with
  | Except.ok st' => Except.ok ⟨st', f.pres st.val _ st.prop h⟩
  | Except.error result => Except.error result

theorem step_coe {st : MatchStack.T' f} : Subtype.val <$> st.step = st.val.step := by
  simp only [step]
  split <;> (
    expose_names;
    simp only [Except.map_ok, Except.map_error]
    exact Eq.symm heq)

theorem step_eq_ok_coe {st st' : MatchStack.T' f}
    : st.step = Except.ok st' ↔ st.val.step = Except.ok st'.val := by
  have adv := st.step_coe
  constructor <;> intro eq
  · simp only [eq, Except.map_ok] at adv; exact Eq.symm adv
  · simp only [eq, ← Except.map_ok] at adv
    rw [map_inj_right Subtype.val_inj.mp] at adv
    exact adv

theorem step_eq_error_coe {st : MatchStack.T' f} {res : PartialMatches w}
    : st.step = Except.error res ↔ st.val.step = Except.error res := by
  have adv := st.step_coe
  constructor <;> intro eq
  · simp only [eq, Except.map_error] at adv; exact Eq.symm adv
  · simp only [eq, ← Except.map_error] at adv
    rw [← Except.map_error Subtype.val, map_inj_right Subtype.val_inj.mp] at adv
    exact adv

theorem step_eq_ok {st st' : MatchStack.T' f} (hst : st.step = Except.ok st')
    : ∃ (ac : Action w) (as : List (Action w)),
        st.val.entries = ac :: as ∧ st'.val = MatchStack.mk
          (entries := (ac.process st.val.arg).entries ++ as)
          (arg := (ac.process st.val.arg).arg)
  := st.val.step_eq_ok (step_eq_ok_coe.mp hst)

theorem step_singleton (ac : Action w) {arg : PartialMatches w}
    (f : Terminator w) (fac : f (ac.matchStack arg))
    : (ac.matchStackT' arg f fac).step = Except.ok ⟨
        ac.process arg, f.pres _ _ fac (step_singleton ac arg)
      ⟩ := by
  rw [step_eq_ok_coe, Action.matchStackT']
  exact MatchStack.step_singleton ac arg

def run (st : MatchStack.T' f) : PartialMatches w :=
  match _ : st.step with
  | Except.ok st' => st'.run
  | Except.error res => res
termination_by st
decreasing_by
  simpa [← step_eq_ok_coe]

end T'

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
