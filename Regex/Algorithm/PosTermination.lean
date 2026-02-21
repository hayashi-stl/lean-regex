import Regex.Algorithm.PosLawful
import Mathlib.Data.Multiset.DershowitzManna
import Regex.Algorithm.Termination

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

-- used for termination
def numRawStars (r : Regex α) : ℕ := match r with
  | bot => 0
  | empty => 0
  | unit _ => 0
  | concat q r => match q, r with
    | filterEmpty false q, star _ r => max q.numRawStars r.numRawStars
    | q, r => max q.numRawStars r.numRawStars
  | or q r => max q.numRawStars r.numRawStars
  | filterEmpty _ r => r.numRawStars
  | star _ r => r.numRawStars + 1
  | start => 0
  | end' => 0
  | capture _ r => r.numRawStars
  | backref _ _ => 0

set_option linter.flexible false in
omit deq in
theorem numRawStars_fst_le_concat (q r : Regex α)
    : q.numRawStars ≤ [/⟨q⟩⟨r⟩/].numRawStars := by
  cases q <;> simp [numRawStars]
  · rw [← or_assoc]
    exact Or.inl (le_total _ _)
  expose_names
  rw (occs := [2]) [numRawStars.eq_def]
  simp
  split <;> expose_names
  · simp at *; simp [heq]
  · rw [numRawStars]; simp

set_option linter.flexible false in
omit deq in
theorem numRawStars_snd_le_concat (q r : Regex α) (hq : ∀ q', q ≠ [/⟨q'⟩ -ε/])
    : r.numRawStars ≤ [/⟨q⟩⟨r⟩/].numRawStars := by
  rw [numRawStars]
  · simp
  · exact fun q' t r' eq ↦ (hq q' eq).elim

-- used for termination
def numBackrefs (r : Regex α) : ℕ := match r with
  | bot => 0
  | empty => 0
  | unit _ => 0
  | concat q r => q.numBackrefs + r.numBackrefs
  | or q r => q.numBackrefs + r.numBackrefs
  | filterEmpty _ r => r.numBackrefs
  | star _ r => r.numBackrefs
  | start => 0
  | end' => 0
  | capture _ r => r.numBackrefs
  | backref _ _ => 1

omit deq in
theorem numRawStars_list (w : List α) : (list w).numRawStars = 0 := by
  induction w with
  | nil => simp [list, numRawStars]
  | cons c cs cind => simp [list, numRawStars, cind]

omit deq in
theorem numBackrefs_list (w : List α) : (list w).numBackrefs = 0 := by
  induction w with
  | nil => simp [list, numBackrefs]
  | cons c cs cind => simp [list, numBackrefs, cind]


/-- A decreasing variable that proves termination of an action -/
structure Action.Terminator where
  distsToEnd : ℕ
  numRawStars : ℕ
  numBackrefs : ℕ
  regexSize : ℕ
  actionSize : ℕ
  concatSize : ℕ
  deriving Repr

def Action.Terminator.toTuple (t : Terminator) :=
  (t.distsToEnd, t.numRawStars, t.numBackrefs, t.regexSize, t.actionSize, t.concatSize)

def Action.terminator (ac : Action w) : Option Terminator := match ac with
  | .regex r s _ => some ⟨s.distToEnd + 1, r.numRawStars, r.numBackrefs, r.depth, 0, 0⟩
  | .concatWait q r s => some ⟨match q with
    | .filterEmpty false _ => s.distToEnd
    | _ => s.distToEnd + 1
    , r.numRawStars, r.numBackrefs, r.depth, 2, 0⟩
  | .concat r s old _ => some ⟨s.distToEnd + 1,
    r.numRawStars, r.numBackrefs, r.depth, 1, old.length⟩
  | .orWait r s _ => some ⟨s.distToEnd + 1, r.numRawStars, r.numBackrefs, r.depth, 1, 0⟩
  | .or _ _ => some ⟨0, 0, 0, 0, 0, 0⟩
  | .filterEmpty _ _ => some ⟨0, 0, 0, 0, 0, 0⟩
  | .capture _ _ => some ⟨0, 0, 0, 0, 0, 0⟩

instance Action.Terminator.instWellFoundedRelation :
    WellFoundedRelation Terminator := invImage toTuple Prod.instWellFoundedRelation

set_option linter.flexible false in
theorem Action.terminator_decreases {ac : Action w} (law : ac.PosLawful)
    {t : Action.Terminator} (ht : ac.terminator = some t)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    {ac' : Action w} (hac' : ac' ∈ (ac.process arg).entries)
    : ∃ t', ac'.terminator = some t' ∧
      Prod.instWellFoundedRelation.rel t'.toTuple t.toTuple := by
  have zerole (n : ℕ) : 0 < n ∨ 0 = n := lt_or_eq_of_le (Nat.zero_le _)
  have zerole' (n : ℕ) : 0 < n ∨ n = 0 := by simp [eq_comm] at zerole; exact zerole n
  have le (a b : ℕ) : (a ≤ b) = (a < b ∨ a = b) := iff_eq_eq ▸ le_iff_lt_or_eq
  simp_wf
  simp only [Terminator.toTuple, Prod.lex_def]
  cases ac <;> (expose_names; simp [terminator] at ht; simp [← ht])
  cases r <;> (expose_names; simp [depth, numRawStars, numBackrefs] at ht ⊢)
  all_goals simp [process] at hac'
  any_goals split at hac'
  all_goals cases ac' <;> expose_names
  any_goals simp at hac'
  any_goals simp [terminator, ← ht] at *
  any_goals simp [hac', zerole', ← le, numRawStars, numBackrefs, depth]
  · exact numRawStars_fst_le_concat _ _
  · split <;> simp
    expose_names; exact numRawStars_snd_le_concat _ _ h
  case regex.or.regex | regex.or.orWait => exact lt_or_ge _ _
  · split <;> simp [numRawStars, numBackrefs]
  · exact ⟨numRawStars_list _, numBackrefs_list _⟩
  · rcases hac' with ⟨_, ⟨nemp, min⟩, _, _⟩
    split <;> expose_names
    · rw [← Icc.distToEnd_lt]
      have filt := lawArg.lt_arg_filterEmpty
      simp [posLawful_lt_arg_filterEmpty] at filt
      have lt : ∀ a ∈ arg.map Prod.fst, s < a := by simp; exact filt
      rw [min, List.lt_min_iff]
      simp
      exact filt
    · rw [← Nat.le_iff_lt_add_one, ← Icc.distToEnd_le]
      have posle := lawArg.le_arg
      simp [posLawful_le_arg, pos] at posle
      have le : ∀ a ∈ arg.map Prod.fst, s ≤ a := by simp; exact posle
      rw [min, List.le_min_iff]
      simp
      exact posle
  · rw [← Icc.distToEnd_le]
    have postr := law.truth
    simp [posLawful_truth] at postr
    exact postr.1

theorem Action.exists_terminator_preserved {ac : Action w} (law : ac.PosLawful)
    (ht : ∃ t, ac.terminator = some t)
    {arg : PartialMatches w} (lawArg : ac.PosLawArg arg)
    : ∀ (ac' : Action w) (_ : ac' ∈ (ac.process arg).entries),
      ∃ t', ac'.terminator = some t' := by
  intro ac' hac'
  rcases ht with ⟨t, ht⟩
  have ⟨t', ht', _⟩ := ac.terminator_decreases law ht lawArg hac'
  exact ⟨t', ht'⟩

theorem MatchStack.terminating_preserved {st : MatchStack w}
    (law : st.PosLawful)
    (term : ∀ ac ∈ st.entries, ∃ t, ac.terminator = some t) {st' : MatchStack w}
    (adv : st.step = Except.ok st')
    : ∀ ac' ∈ st'.entries, ∃ t, ac'.terminator = some t := by
  obtain ⟨ac, as, steq, st'eq⟩ := MatchStack.step_eq_ok adv
  simp only [st'eq, List.mem_append]
  intro ac' mem
  rcases mem with mem | mem
  · obtain ⟨_, law, lawArg, _⟩ := law
    simp only [posLawful_lawful_actions, posLawful_posLawArg_fst] at law lawArg
    simp only [steq, List.mem_cons, forall_eq_or_imp, List.cons.injEq, and_imp,
      forall_apply_eq_imp_iff, forall_eq'] at *
    obtain ⟨⟨t, teq⟩, _⟩ := term
    have ⟨t', t'stuff⟩ := ac.terminator_decreases law.1 teq lawArg mem
    exact ⟨t', t'stuff.1⟩
  · simp only [steq, List.mem_cons, forall_eq_or_imp] at *
    exact term.2 ac' mem

def Action.posLawArg_nil (ac : Action w) : ac.PosLawArg [] := by
  apply PosLawArg.mk
  all_goals simp only [posLawful_le_arg, posLawful_lt_arg_filterEmpty, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true]
  split <;> trivial

def Action.PosLaw : Law w where
  toFun ac arg := ac.PosLawful ∧ ac.PosLawArg arg ∧ ∃ t, ac.terminator = some t
  --
  term ac arg law := by
    obtain ⟨law, lawarg, t, term⟩ := law
    apply Subrelation.accessible (r := fun ac' ac ↦
      ∃ t' t, ac'.terminator = some t' ∧ ac.terminator = some t ∧
        Prod.instWellFoundedRelation.rel t'.toTuple t.toTuple)
    · simp only [Subrelation, exists_and_left]
      intro ac' ac inv
      rw [InvStep] at inv
      obtain ⟨arg, ⟨law, lawarg, ⟨t, term⟩⟩, mem⟩ := inv
      obtain ⟨t', term', wf⟩ := ac.terminator_decreases law term lawarg mem
      exact ⟨t', term', t, term, wf⟩
    rw [show (fun ac' ac : Action w ↦
      ∃ t' t, ac'.terminator = some t' ∧ ac.terminator = some t ∧
        WellFoundedRelation.rel t'.toTuple t.toTuple) = InvImage
        (fun t₀' t₀ : Option Terminator ↦ ∃ t' t, t₀' = some t' ∧ t₀ = some t ∧
        WellFoundedRelation.rel t'.toTuple t.toTuple) terminator by rfl]
    apply InvImage.accessible terminator
    simp only [(eq_comm : _ = some _ ↔ _)]
    apply WellFounded.image_acc' (Option.some_injective _)
      (WellFounded.apply WellFoundedRelation.wf t) (Eq.symm term)
  --
  push ac arg law ac' as' hac' := by
    obtain ⟨law, lawarg, t, term⟩ := law
    obtain ⟨law', lawarg'⟩ := posLawful_preserved law lawarg
    have mem := hac' ▸ List.mem_cons_self
    obtain ⟨t', term', wf⟩ := ac.terminator_decreases law term lawarg mem
    refine ⟨⟨law' ac' mem, lawarg' ac' as' hac', ⟨t', term'⟩⟩, ?_⟩
    intro a mem'
    have mem' := hac' ▸ List.mem_cons_of_mem _ mem'
    obtain ⟨t', term', wf⟩ := ac.terminator_decreases law term lawarg mem'
    exact ⟨[], law' a mem', a.posLawArg_nil, ⟨t', term'⟩⟩
  --
  pop ac arg law n ac1 ac2 as arg' stepn emp := by
    have stlaw := ac.matchStack_posLawful law.1 law.2.1
    rw [matchStack] at stepn
    have hst (st st' : MatchStack w) (n : ℕ) (law : st.PosLawful)
        (term : ∀ ac ∈ st.entries, ∃ t, ac.terminator = some t)
        (hst : st.stepN n = Except.ok st')
        : st'.PosLawful ∧ ∀ ac ∈ st'.entries, ∃ t, ac.terminator = some t := by
      induction n generalizing st st' with
      | zero =>
        rw [MatchStack.step0_eq_self, Except.ok.injEq] at hst
        exact ⟨hst ▸ law, hst ▸ term⟩
      | succ n ind =>
        obtain ⟨st_, stepn_, st_eq⟩ := MatchStack.stepN_step_of_stepN_add_one hst
        specialize ind st st_ law term stepn_
        exact ⟨st_.posLawful_preserved ind.1 st_eq,
          st_.terminating_preserved ind.1 ind.2 st_eq⟩
    obtain ⟨law, term⟩ := hst (MatchStack.mk [ac] arg)
      (MatchStack.mk (ac1 :: ac2 :: as) arg') n stlaw (by simp [law.2.2]) stepn
    have aclaw := law.lawful_actions
    simp only [MatchStack.posLawful_lawful_actions, List.mem_cons,
      forall_eq_or_imp] at aclaw
    have steq : (MatchStack.mk (ac1 :: ac2 :: as) arg').step =
        Except.ok (MatchStack.mk (ac2 :: as) (ac1.process arg').arg) := by
      simp [MatchStack.step, emp]
    have law' := MatchStack.posLawful_preserved_posLawArg_fst law steq
    simp only [MatchStack.posLawful_posLawArg_fst, List.cons.injEq, and_imp,
      forall_apply_eq_imp_iff, forall_eq', List.mem_cons, forall_eq_or_imp] at law' term
    exact ⟨aclaw.2.1, law', term.2.1⟩

end Regex
