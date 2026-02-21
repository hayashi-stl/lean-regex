import Regex.Algorithm.Defs
import Regex.List

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace Action
variable (ac : Action w) (arg : PartialMatches w)

/-- The argument is at least as far into the sequence as the action -/
def posLawful_le_arg := ∀ ent ∈ arg, ac.pos ≤ ent.1

/-- A `Action.concatWait` waiting for a `filterEmpty false` actually
receives only nonempty matches -/
def posLawful_lt_arg_filterEmpty := match ac with
  | .concatWait [/⟨_⟩ -ε/] _ s => ∀ ent ∈ arg, s < ent.fst
  | _ => True

/-- `Action.concat` and `Action.or` tells the truth about its position -/
def posLawful_truth := match ac with
  | .concat _ s old new => ∀ ent ∈ old ++ new, s ≤ ent.fst
  | .or s fst => ∀ ent ∈ fst, s ≤ ent.fst
  | _ => True

/-- A structure asserting restrictions on actions and their arguments. -/
structure PosLawArg where
  le_arg : posLawful_le_arg ac arg
  lt_arg_filterEmpty : posLawful_lt_arg_filterEmpty ac arg

/-- A structure asserting restrictions on actions, without involving arguments -/
structure PosLawful where
  truth : posLawful_truth ac

end Action

-- Too many simps here to expand
set_option linter.flexible false in
theorem Action.pos_arg_le {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} (hac' : ac' ∈ (ac.process arg).entries)
    : ac.pos ≤ ac'.pos ∧
      ∀ ret ∈ (ac.process arg).arg, ac'.pos ≤ ret.fst := by
  obtain ⟨harg, _⟩ := lawArg
  obtain ⟨hcon⟩ := law
  simp [posLawful_le_arg, posLawful_truth] at harg hcon
  cases ac <;> (expose_names; simp [pos] at hac' harg hcon ⊢)
  -- simplify `process` everywhere except at the regex
  focus have kaboom := Eq.refl (regex r s cap)
  all_goals first | (fail_if_success rw [kaboom] at hac'); simp [process] at hac' | skip
  induction r <;> (expose_names; simp [process] at hac' ⊢)
  case' regex.star => cases t <;> simp at hac' ⊢
  all_goals split <;> expose_names
  any_goals simp at hac'
  any_goals simp at r_ih
  any_goals split at hac'
  any_goals simp at hac'
  any_goals simp [process]
  any_goals simp [hac']
  · rcases hac' with ⟨ar, ⟨nemp, min⟩, a2arg, a3emp⟩
    rw [min, List.le_min_iff]
    simp
    exact harg
  · expose_names
    specialize hcon s' cap
    simp at hcon
    exact hcon

-- Too many simps here to expand
set_option linter.flexible false in
/-- the version without ac', in case an action returns no new actions to be done -/
theorem Action.pos_arg_le' {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ret : Pos w × Captures w} (hret : ret ∈ (ac.process arg).arg)
    : ac.pos ≤ ret.fst := by
  obtain ⟨harg, _⟩ := lawArg
  obtain ⟨hcon⟩ := law
  simp [posLawful_le_arg, posLawful_truth] at harg hcon
  cases ac <;> (expose_names; simp [pos] at harg hcon ⊢)
  focus have kaboom := Eq.refl (regex r s cap)
  all_goals first | (fail_if_success rw [kaboom] at hret); simp [process] at hret | skip
  cases r <;> (expose_names; simp [process] at hret ⊢)
  case' regex.star => cases t <;> simp at hret ⊢
  all_goals rcases ret with ⟨s', cap⟩; simp at *
  any_goals simp [← hret]
  · rcases hret with ⟨⟨cap, eq⟩, _⟩
    simp [eq, Icc.val_le_val]
  · cases old <;> (expose_names; simp at hret hcon)
    rcases hret with hret | hret
    · exact hcon s' cap hret
    · exact harg s' cap hret
  · rcases hret with hret | hret
    · exact hcon s' cap hret
    · exact harg s' cap hret
  · exact harg s' cap hret.left
  · rcases hret with ⟨cap, hret, _⟩
    exact harg s' cap hret

theorem Action.pos_le {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} (hac' : ac' ∈ (ac.process arg).entries)
    : ac.pos ≤ ac'.pos := (ac.pos_arg_le law lawArg hac').left

-- Too many simps here to expand
set_option linter.flexible false in
theorem Action.entries_pos_sorted {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    (i : Fin (ac.process arg).entries.length) (j : Fin i)
    : (ac.process arg).entries[i].pos ≤ (ac.process arg).entries[j].pos := by
  -- Avoid dealing with annoying type intensionality
  obtain ⟨i, ilt⟩ := i
  obtain ⟨j, jlt⟩ := j
  cases ac
  all_goals expose_names
  cases r
  all_goals expose_names
  any_goals simp [process] at ilt jlt ⊢
  any_goals split
  any_goals simp at ilt ⊢
  case' concatWait.isTrue => split at ilt <;> simp at ilt
  all_goals (obtain ⟨j0, i1⟩ : j = 0 ∧ i = 1 := by omega); simp [j0, i1, pos]
  expose_names
  obtain ⟨hcon⟩ := law
  simp [posLawful_truth] at hcon
  exact hcon.left

set_option linter.flexible false in
theorem Action.posLawful_preserved_le_arg {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} {as : List (Action w)} (hac' : (ac.process arg).entries = ac' :: as)
    : ac'.posLawful_le_arg (ac.process arg).arg := by
  exact (pos_arg_le law lawArg (hac' ▸ List.mem_cons_self)).right

set_option linter.flexible false in
theorem Action.posLawful_preserved_lt_arg_filterEmpty {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} {as : List (Action w)} (hac' : (ac.process arg).entries = ac' :: as)
    : ac'.posLawful_lt_arg_filterEmpty (ac.process arg).arg := by
  simp [posLawful_lt_arg_filterEmpty]
  split <;> try trivial
  cases ac <;> (expose_names)
  cases r_2 <;> (expose_names)
  all_goals simp [process] at hac' ⊢
  all_goals split <;> simp at hac' ⊢

set_option linter.flexible false in
theorem Action.posLawful_preserved_truth {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} (hac' : ac' ∈ (ac.process arg).entries)
    : ac'.posLawful_truth := by
  obtain law' := law
  obtain lawArg' := lawArg
  obtain ⟨postr⟩ := law
  obtain ⟨posle⟩ := lawArg
  simp only [posLawful_le_arg, posLawful_truth] at *
  cases ac <;> (expose_names)
  cases r <;> (expose_names)
  all_goals simp [process, pos] at postr posle hac' ⊢
  case' regex.star => cases t <;> (simp at hac')
  any_goals simp [hac']
  any_goals split <;> (expose_names)
  any_goals simp at hac'
  any_goals trivial
  · intro s' cap' mem
    rcases hac' with ⟨r1r, ⟨nemp, min⟩, oldarg, newemp⟩
    simp [newemp, min, oldarg] at mem ⊢
    have mem1 : s' ∈ arg.map Prod.fst := by simp; exact ⟨cap', mem⟩
    exact List.min_le_of_mem mem1
  · split at hac' <;> (expose_names; simp at postr hac' ⊢)
    simp [hac'.2.2.2, ← or_assoc]
    simp only [or_assoc] at postr
    intro s'' cap' memor
    rcases memor with mem | mem
    · exact hac'.2.1 ▸ postr s'' cap' (Or.inr (hac'.2.2.1 ▸ mem))
    · exact hac'.2.1 ▸ posle s'' cap' mem
  · split at hac' <;> simp at hac'
  · exact fun s' cap mem ↦ hac'.1 ▸ posle s' cap (hac'.2 ▸ mem)

-- Too many simps here to expand
set_option linter.flexible false in
theorem Action.posLawful_preserved {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    : (∀ ac' ∈ (ac.process arg).entries, ac'.PosLawful) ∧
      (∀ ac' as, (ac.process arg).entries = ac' :: as
        → ac'.PosLawArg (ac.process arg).arg) := by
  constructor
  · exact fun ac' mem ↦ ⟨ac.posLawful_preserved_truth law lawArg mem⟩
  · exact fun ac' as cons ↦ ⟨
      ac.posLawful_preserved_le_arg law lawArg cons,
      ac.posLawful_preserved_lt_arg_filterEmpty law lawArg cons,
    ⟩

section Lawful
namespace MatchStack
variable (st : MatchStack w)

def posLawful_sorted := ∀ i : Fin st.entries.length,
  ∀ j : Fin i, st.entries[i].pos ≤ st.entries[j].pos

def posLawful_lawful_actions := ∀ ac, ac ∈ st.entries → ac.PosLawful

def posLawful_posLawArg_fst := ∀ ac as, st.entries = ac :: as → ac.PosLawArg st.arg

def posLawful_consecutive := ∀ i : Fin st.entries.length,
  (bound : i.val + 1 < st.entries.length) →
  match st.entries[i.val + 1] with
  | .concatWait [/⟨_⟩ -ε/] _ _ => match st.entries[i] with
    | .regex [/⟨_⟩ -ε/] _ _ => True
    | .filterEmpty false _ => True
    | _ => False
  | _ => True

structure PosLawful (st : MatchStack w) where
  sorted : st.posLawful_sorted
  lawful_actions : st.posLawful_lawful_actions
  posLawArg_fst : st.posLawful_posLawArg_fst
  consecutive : st.posLawful_consecutive

end MatchStack
end Lawful

theorem MatchStack.posLawful_preserved_sorted {st : MatchStack w} (law : st.PosLawful)
    {st' : MatchStack w} (hst : st.step = Except.ok st')
    : st'.posLawful_sorted := by
  obtain ⟨ac, as', has, hst⟩ := step_eq_ok hst
  obtain ⟨sort, lawac, lawarg, con⟩ := law
  simp only [posLawful_sorted, posLawful_lawful_actions, posLawful_posLawArg_fst] at *
  simp only [has, Fin.getElem_fin, List.mem_cons, forall_eq_or_imp, List.cons.injEq,
    and_imp, forall_apply_eq_imp_iff, forall_eq', hst] at sort lawac lawarg ⊢
  rintro ⟨i, ilt⟩ ⟨j, jlt⟩
  by_cases! ilt' : i < (ac.process st.arg).entries.length
  · rw [List.getElem_append_left ilt', List.getElem_append_left (.trans jlt ilt')]
    exact ac.entries_pos_sorted lawac.1 lawarg ⟨i, ilt'⟩ ⟨j, jlt⟩
  have up (k : ℕ) (kge : (ac.process st.arg).entries.length ≤ k)
      (klt : k < st'.entries.length) :
      k - (ac.process st.arg).entries.length + 1 < st.entries.length := by
    simp only [hst, List.length_append, has, List.length_cons,
      Order.lt_add_one_iff, Order.add_one_le_iff] at klt ⊢
    rwa [Nat.sub_lt_iff_lt_add kge, add_comm]
  specialize sort ⟨i - (ac.process st.arg).entries.length + 1, up i ilt' ilt⟩
  rw [List.getElem_cons_succ] at sort
  rw [List.getElem_append_right ilt']
  by_cases! jlt' : j < (ac.process st.arg).entries.length
  · rw [List.getElem_append_left jlt']
    specialize sort ⟨0, Nat.zero_lt_succ _⟩
    rw [List.getElem_cons_zero] at sort
    exact .trans sort (ac.pos_le lawac.1 lawarg (List.getElem_mem jlt'))
  · specialize sort ⟨j - (ac.process st.arg).entries.length + 1,
      Nat.add_lt_add_right (Nat.sub_lt_sub_right jlt' jlt) 1⟩
    rw [List.getElem_cons_succ] at sort
    rwa [List.getElem_append_right jlt']

theorem MatchStack.posLawful_preserved_lawful_actions {st : MatchStack w} (law : st.PosLawful)
    {st' : MatchStack w} (hst : st.step = Except.ok st')
    : st'.posLawful_lawful_actions := by
  obtain ⟨ac, as', has, hst⟩ := step_eq_ok hst
  obtain ⟨_, lawac, lawarg, _⟩ := law
  simp only [posLawful_lawful_actions, posLawful_posLawArg_fst] at *
  simp only [hst, List.mem_append]
  simp only [has, List.mem_cons, forall_eq_or_imp] at lawac
  intro ac' memor
  rcases memor with mem | mem
  · exact (ac.posLawful_preserved lawac.1 (lawarg ac as' has)).1 _ mem
  · exact lawac.2 ac' mem

theorem MatchStack.posLawful_preserved_posLawArg_fst {st : MatchStack w} (law : st.PosLawful)
    {st' : MatchStack w} (hst : st.step = Except.ok st')
    : st'.posLawful_posLawArg_fst := by
  obtain ⟨ac, as, has, hst⟩ := step_eq_ok hst
  obtain ⟨sorted, lawac, lawarg, con⟩ := law
  simp only [posLawful_sorted,
    posLawful_lawful_actions, posLawful_posLawArg_fst, posLawful_consecutive] at *
  simp only [hst]
  simp only [has, Fin.getElem_fin, List.mem_cons, forall_eq_or_imp, List.cons.injEq,
    and_imp, forall_apply_eq_imp_iff, forall_eq', List.length_cons, Order.lt_add_one_iff,
    Order.add_one_le_iff, List.getElem_cons_succ] at sorted lawac lawarg con
  by_cases! lemp : (ac.process st.arg).entries ≠ []
  · obtain ⟨ac', as', ac'eq⟩ := List.ne_nil_iff_exists_cons.mp lemp
    simp only [ac'eq, List.cons_append, List.cons.injEq, and_imp,
      forall_apply_eq_imp_iff, forall_eq']
    exact (ac.posLawful_preserved lawac.1 lawarg).2 ac' as' ac'eq
  simp only [lemp, List.nil_append]
  intro ac' as' aseq
  have two : 1 < st.entries.length := by
    rw [aseq] at has
    apply_fun List.length at has; simp only [List.length_cons] at has; linarith
  apply Action.PosLawArg.mk
  · simp only [Action.posLawful_le_arg, Prod.forall]
    intro s cap smem
    specialize sorted ⟨1, two⟩ ⟨0, zero_lt_one⟩
    simp only [aseq, List.getElem_cons_succ, List.getElem_cons_zero] at sorted
    exact .trans sorted (ac.pos_arg_le' lawac.1 lawarg smem)
  · simp only [Action.posLawful_lt_arg_filterEmpty]
    split <;> try trivial
    expose_names
    intro ⟨s', cap'⟩ entmem; simp only []
    specialize con ⟨0, List.length_pos_iff_exists_cons.mpr ⟨ac, as, has⟩⟩
      (List.length_pos_iff_exists_cons.mpr ⟨_, as', aseq⟩)
    simp only [aseq, List.getElem_cons_zero] at con
    split at con <;> try contradiction
    specialize sorted ⟨1, two⟩ ⟨0, zero_lt_one⟩
    simp only [Action.pos, aseq, List.getElem_cons_succ, List.getElem_cons_zero] at sorted
    have le := Action.pos_arg_le' lawac.1 lawarg entmem
    simp only [Action.process, Bool.false_eq_true, eq_iff_iff, iff_false, decide_not,
      List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at entmem
    simp only [Action.pos] at le
    exact trans sorted (lt_of_le_of_ne le entmem.2)

set_option linter.flexible false in
theorem MatchStack.posLawful_preserved_consecutive {st : MatchStack w} (law : st.PosLawful)
    {st' : MatchStack w} (hst : st.step = Except.ok st')
    : st'.posLawful_consecutive := by
  obtain ⟨ac, as, has, hst⟩ := step_eq_ok hst
  obtain ⟨_, lawac, lawarg, con⟩ := law
  simp only [posLawful_lawful_actions, posLawful_posLawArg_fst, posLawful_consecutive] at *
  simp [hst]
  simp [has] at lawac lawarg con
  intro i i1lt
  by_cases! ilt : i + 1 < (ac.process st.arg).entries.length
  · rw [List.getElem_append_left ilt, List.getElem_append_left
      (.trans (Nat.lt_add_one _) ilt)]
    split <;> (expose_names; try trivial)
    cases ac <;> expose_names
    cases r_2 <;> expose_names
    all_goals simp [Action.process] at ilt i1lt heq ⊢; try contradiction
    any_goals split at heq <;> simp at heq ⊢ <;> try contradiction
    · simp [show i.val = 0 by linarith, heq]
    · split at heq <;> (try simp [List.getElem_nil] at heq)
  rw [List.getElem_append_right ilt]
  by_cases! ieq : i + 1 = (ac.process st.arg).entries.length
  · cases as <;> simp at i1lt <;> try linarith
    expose_names
    specialize con ⟨0, List.length_pos_iff_exists_cons.mpr ⟨_, _, has⟩⟩
      (List.length_cons ▸ Nat.zero_lt_succ _)
    simp [List.getElem_append_left (Nat.lt_of_add_one_le (le_of_eq ieq)), ieq]
    simp only [Nat.eq_sub_of_add_eq ieq]
    rw [← List.getLast_eq_getElem (List.length_pos_iff.mp (by linarith))]
    simp at con
    split at con <;> try trivial
    split at con <;> try contradiction
    simp [Action.process]
  · have ile := Nat.le_of_lt_add_one (lt_of_le_of_ne ilt (Ne.symm ieq))
    rw [List.getElem_append_right ile]
    have ilt' : i.val - (ac.process st.arg).entries.length + 1 < as.length := by
      rw [← Nat.sub_add_comm ile]
      rwa [Nat.sub_lt_iff_lt_add ilt, add_comm as.length]
    specialize con ⟨i - (ac.process st.arg).entries.length + 1, .trans ilt'
      (by rw [has, List.length_cons]; exact Nat.lt_add_one _)⟩ ilt'
    simp at con
    simp [Nat.sub_add_comm ile]
    exact con

theorem MatchStack.posLawful_preserved {st : MatchStack w} (law : st.PosLawful)
    {st' : MatchStack w} (hst : st.step = Except.ok st')
    : st'.PosLawful := ⟨
      st.posLawful_preserved_sorted law hst,
      st.posLawful_preserved_lawful_actions law hst,
      st.posLawful_preserved_posLawArg_fst law hst,
      st.posLawful_preserved_consecutive law hst
    ⟩

omit deq in
theorem Action.matchStack_posLawful {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    : (MatchStack.mk [ac] arg).PosLawful := by
  apply MatchStack.PosLawful.mk
  · simp [MatchStack.posLawful_sorted]
  · simp [MatchStack.posLawful_lawful_actions, law]
  · simp [MatchStack.posLawful_posLawArg_fst, lawArg]
  · simp [MatchStack.posLawful_consecutive]

theorem Action.matchStack_posLawful_preserved {ac : Action w} (law : ac.PosLawful)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    : (ac.process arg).PosLawful := by
  have st' := MatchStack.step_singleton ac arg
  have hst := ac.matchStack_posLawful law lawArg
  exact (MatchStack.mk [ac] arg).posLawful_preserved hst st'

end Regex
