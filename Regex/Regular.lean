import Regex.Lemmas.Bounds
import Regex.Lemmas.Monotone
import Regex.Match
import Regex.Termination

variable {α : Type u}

namespace List

/-- The flattening of a list of lists is either empty or
there's a nonempty list that could have been first without changing the result. -/
theorem flatten_eq_nil_or_rec (L : List (List α))
    : L.flatten = [] ∨
      ∃ (A : List (List α)) (l : List α) (B : List (List α)),
        l ≠ [] ∧ L = A ++ l :: B ∧ L.flatten = l ++ B.flatten := by
  rw [or_iff_not_imp_left]
  intro nemp
  rw [← ne_eq, List.flatten_ne_nil_iff, List.exists_mem_iff_getElem] at nemp
  have min := WellFounded.has_min (wellFounded_lt (α := ℕ))
    {i | ∃ (x : i < L.length), L[i] ≠ []} nemp
  simp only [Set.mem_setOf_eq, not_lt, forall_exists_index] at min
  have ⟨i, ⟨ilt, inemp⟩, lti⟩ := min
  use L.take i, L[i], L.drop (i + 1), inemp
  simp only [getElem_cons_drop, take_append_drop, true_and]
  have flt : L.flatten = (L.take i).flatten ++ L[i] ++ (L.drop (i + 1)).flatten := by
    have flt : L.flatten = (L.take i ++ L[i] :: L.drop (i + 1)).flatten := by simp
    rw [flt, List.flatten_append, List.flatten_cons, List.append_assoc]
  have emp : ∀ a ∈ take i L, a = [] := by
    rw [← List.forall_getElem]
    intro i' i'lt
    simp only [length_take, lt_inf_iff] at i'lt
    conv at lti in _ → _ => rw [ne_eq, not_imp_comm]; push_neg
    specialize lti i' i'lt.2 i'lt.1
    rwa [List.getElem_take]
  rw [List.flatten_eq_nil_iff.mpr emp] at flt
  simpa using flt

--/-- "Strong induction" on lists -/
--def strongRec {motive : List α → Sort*}
--    (ind : ∀)

end List

namespace Language

/-- A recursive membership predicate for kstar -/
theorem mem_kstar_iff_rec {l : Language α} {x : List α}
    : x ∈ KStar.kstar l ↔ x = [] ∨
      ∃ a b : List α, x = a ++ b ∧ a ≠ [] ∧ a ∈ l ∧ b ∈ KStar.kstar l := by
  rw [mem_kstar]
  constructor
  · rw [or_iff_not_imp_left]
    rintro ⟨L, xL, yL⟩ nemp
    have flt := List.flatten_eq_nil_or_rec L
    rw [← xL, or_iff_not_imp_left] at flt
    have ⟨A, k, B, knemp, comp, xeq⟩ := flt nemp
    simp only [comp, List.mem_append, List.mem_cons] at yL
    use k, B.flatten, xeq, knemp, (yL k (Or.inr (Or.inl rfl)))
    rw [mem_kstar]
    refine ⟨B, rfl, fun y yB ↦ (yL y (Or.inr (Or.inr yB)))⟩
  · rintro (emp | ⟨a, b, xeq, nemp, al, star⟩)
    · use []; simp [emp]
    · have ⟨L', bL', yL'⟩ := mem_kstar.mp star
      use a :: L'
      simp only [List.flatten_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨bL' ▸ xeq, al, yL'⟩

end Language

variable [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace Regex

/-- Whether a language is truly regular or just a faker. This is
why it's good to separate `Regex` from `RegularExpression`. -/
def Regular (r : Regex α) (term : ∀ w, r.Terminates w 0 0)
  := ∃ r' : RegularExpression α, r.language term = r'.matches'

/-- The classic regular expression operators -/
inductive CRegular : Regex α → Prop where
  | bot : CRegular bot
  | empty : CRegular empty
  | unit c : CRegular (unit c)
  | concat q r : CRegular q → CRegular r → CRegular (concat q r)
  | or q r : CRegular q → CRegular r → CRegular (or q r)
  | star t r : CRegular r → CRegular (star t r)

/-- A regex where `partialMatch` does not care about outside context
like captures.
Proving/using a tailored termination condition has proved to be difficult,
so this predicate requires the regex to always terminate. -/
def MatchPartialFree (r : Regex α) :=
  ∃ term : r.AllTerminates,
  ∀ w s cap mat, mat ∈ r.matchPartial w s cap (term w s cap) →
    ∀ (wa wb : List α) cap₁,
    ∃ cap₁', ((wa ++ w.extract s mat.1).length, cap₁') ∈
      r.matchPartial (wa ++ w.extract s mat.1 ++ wb) wa.length cap₁ (term _ _ _)

theorem matchPartialFree_bot : MatchPartialFree ([/⊥/] : Regex α) := by
  simp [MatchPartialFree, matchPartial_bot, allTerminates_bot]

theorem matchPartialFree_empty : MatchPartialFree ([//] : Regex α) := by
  simp [MatchPartialFree, matchPartial_empty, allTerminates_empty]

theorem matchPartialFree_unit {c : α} : MatchPartialFree [/c/] := by
  simp only [MatchPartialFree, matchPartial_unit, List.mem_ite_nil_right, List.mem_cons,
    List.not_mem_nil, or_false, List.extract_eq_drop_take, List.append_assoc, List.length_append,
    List.length_take, List.length_drop, Prod.mk.injEq, Nat.add_left_cancel_iff, exists_and_left,
    ↓existsAndEq, and_true, forall_const, and_imp, forall_eq_apply_imp_iff, add_tsub_cancel_left,
    inf_eq_left, allTerminates_unit, exists_const]
  intro w s wsc wa wb
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  have ⟨slt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
  rw [List.getElem?_append_left (by simp [slt])]
  simp [wsc, Nat.add_one_le_of_lt (Nat.zero_lt_sub_of_lt slt)]

theorem matchPartialFree_concat {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, forall_exists_index, Prod.forall]
  refine ⟨allTerminates_concat qf.1 rf.1, ?_⟩
  intro w s cap s'' cap'' s' cap' qmem rmem wa wb cap₁
  have qf := qf.2 _ _ _ _ qmem wa (w.extract s' s'' ++ wb) cap₁
  have qm := monotone _ _ _ _ _ qmem
  have rm := monotone _ _ _ _ _ rmem
  rw! [List.extract_append_extract_assoc_right _ qm rm] at qf
  have ⟨cap₁', qmem₁⟩ := qf
  have rf := rf.2 _ _ _ _ rmem (wa ++ w.extract s s') wb cap₁'
  rw! [List.extract_append_extract_assoc_left _ qm rm] at rf
  have ⟨cap₁'', rmem₁⟩ := rf
  rw! [List.append_assoc _ (w.extract s s'), List.extract_append_extract _ qm rm] at rmem₁
  exact ⟨_, _, _, qmem₁, rmem₁⟩

theorem matchPartialFree_or {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ | ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_or, List.mem_append, Prod.forall]
  refine ⟨allTerminates_or qf.1 rf.1, ?_⟩
  intro w s cap s' cap' mem wa wb cap₁
  rcases mem with mem | mem
  · have ⟨cap₁', mem'⟩ := qf.2 _ _ _ _ mem wa wb cap₁
    exact ⟨cap₁', Or.inl mem'⟩
  · have ⟨cap₁', mem'⟩ := rf.2 _ _ _ _ mem wa wb cap₁
    exact ⟨cap₁', Or.inr mem'⟩

theorem matchPartialFree_filterEmpty {e : Bool} {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩ ‹e›ε/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff,
    Bool.decide_iff_dist, Bool.decide_eq_true, List.mem_filter, beq_iff_eq,
    and_imp, Prod.forall]
  refine ⟨allTerminates_filterEmpty rf.1, ?_⟩
  intro w s cap s' cap' mem dec wa wb cap₁
  have ⟨cap₁', mem₁⟩ := rf.2 _ _ _ _ mem wa wb cap₁
  refine ⟨cap₁', mem₁, ?_⟩
  cases e with
  | false =>
    simp only [decide_eq_false_iff_not, not_le, List.extract_eq_drop_take, List.length_append,
      List.length_take, List.length_drop, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      Nat.min_eq_zero_iff, Bool.decide_or, Bool.or_eq_false_iff] at dec ⊢
    refine ⟨fun eq ↦ not_lt.mpr (Nat.sub_eq_zero_iff_le.mp eq) dec, ?_⟩
    by_contra!
    rw [Nat.sub_eq_zero_iff_le] at this
    have bound := matchPartial_outOfBounds_eq this mem
    linarith
  | true =>
    simp only [decide_eq_true_eq, List.extract_eq_drop_take, List.length_append, List.length_take,
      List.length_drop, add_le_iff_nonpos_right, nonpos_iff_eq_zero, Nat.min_eq_zero_iff,
      Bool.decide_or, Bool.or_eq_true] at dec ⊢
    have mono := monotone _ _ _ _ _ mem
    have eq := le_antisymm mono dec
    simp [eq]

/- Helper lemma to avoid managing the greedy/lazy cases at the same time -/
-- Actually, forgot about star difference...
theorem matchPartialFree_or_comm {q r : Regex α} (mpf : [/⟨q⟩ | ⟨r⟩/].MatchPartialFree)
    : [/⟨r⟩ | ⟨q⟩/].MatchPartialFree := by
  rw! [MatchPartialFree, allTerminates_or_comm]
  simp only [mem_matchPartial_or_comm (q := r)]
  exact mpf

theorem matchPartialFree_star_greedy {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩*/].MatchPartialFree := by
  refine ⟨allTerminates_star rf.1, ?_⟩
  intro w s
  by_cases! sle : s ≤ w.length
  · induction s, sle using decreasingStrongRec with | ind s sle ind =>
      simp only [matchPartial_star]
      simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
        matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
        List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
        List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq, Prod.forall]
      intro cap s'' cap'' mem wa wb cap₁
      rcases mem with (mem | ⟨s', cap', mem, mem'⟩) | eq
      · have ⟨cap₁', mem₁⟩ := rf.2 _ _ _ _ mem.1 wa wb cap₁
        refine ⟨_, Or.inl (Or.inl ⟨mem₁, ?_⟩)⟩
        have eq := le_antisymm mem.2 (monotone _ _ _ _ _ mem.1)
        simp [eq]
      · have s'le := endInBounds _ _ sle _ _ _ mem.1
        have rf := rf.2 _ _ _ _ mem.1 wa (w.extract s' s'' ++ wb) cap₁
        have rm := monotone _ _ _ _ _ mem.1
        have rm' := monotone _ _ _ _ _ mem'
        rw! [List.extract_append_extract_assoc_right _ rm rm'] at rf
        have ⟨cap₁', mem₁⟩ := rf
        specialize ind s' s'le mem.2 _ _ mem' (wa ++ w.extract s s') wb cap₁'
        rw! [List.extract_append_extract_assoc_left _ rm rm'] at ind
        have ⟨cap₁'', mem₁'⟩ := ind
        rw! [List.append_assoc _ (w.extract s s'), List.extract_append_extract _ rm rm'] at mem₁'
        refine ⟨cap₁'', Or.inl (Or.inr ⟨_, _, ⟨mem₁, ?_⟩, mem₁'⟩)⟩
        suffices s < s' ∧ s < w.length by simpa
        exact ⟨mem.2, trans mem.2 s'le⟩
      · refine ⟨cap₁, Or.inr ?_⟩
        simp [eq]
  · intro cap mat mem wa wb cap₁
    have bound := matchPartial_outOfBounds_eq (le_of_lt sle) mem
    use cap₁
    simp [bound, matchPartial_star, matchPartial_or, matchPartial_empty]

theorem matchPartialFree_star_greedy_iff_lazy {r : Regex α}
    : [/⟨r⟩*/].MatchPartialFree ↔ [/⟨r⟩*?/].MatchPartialFree := by
  rw! [MatchPartialFree, MatchPartialFree, allTerminates_star_greedy_iff_lazy]
  simp only [matchPartial_star, mem_matchPartial_or_comm (q := [//])]
  simp only [matchPartial_or, matchPartial_concat, matchPartial_empty]
  simp only [List.mem_append, List.mem_flatten, List.mem_pmap, ↓existsAndEq,
    mem_matchPartial_star_greedy_iff_lazy]

theorem matchPartialFree_star {t : StarType} {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩*‹t›/].MatchPartialFree := by
  cases t with
  | greedy => exact matchPartialFree_star_greedy rf
  | lazy => exact matchPartialFree_star_greedy_iff_lazy.mp (matchPartialFree_star_greedy rf)

/-- The classic regular operators are match-partial-free. -/
theorem CRegular.matchPartialFree {r : Regex α} (hr : r.CRegular)
    : r.MatchPartialFree := by
  induction hr with
  | bot => exact matchPartialFree_bot
  | empty => exact matchPartialFree_empty
  | unit _ => exact matchPartialFree_unit
  | concat _ _ _ _ qind rind => exact matchPartialFree_concat qind rind
  | or _ _ _ _ qind rind => exact matchPartialFree_or qind rind
  | star _ _ _ rind => exact matchPartialFree_star rind

theorem MatchPartialFree.match'_ne_nil {r : Regex α} (rf : r.MatchPartialFree)
    {w} {s} {cap} {mat} (mem : mat ∈ r.matchPartial w s cap (rf.1 w s cap))
    : r.match' (w.extract s mat.1) (rf.1 _ _ _) ≠ [] := by
  have ⟨cap₁', rf⟩ := rf.2 _ _ _ _ mem [] [] 0
  simp only [List.nil_append, List.append_nil, List.length_nil] at rf
  rw [← mem_match'_iff_length_mem] at rf
  exact List.ne_nil_of_mem rf

theorem MatchPartialFree.isMatch {r : Regex α} (rf : r.MatchPartialFree)
    {w} {s} {cap} {mat} (mem : mat ∈ r.matchPartial w s cap (rf.1 w s cap))
    : r.IsMatch (w.extract s mat.1) (rf.1 _ _ _) := by
  exact rf.match'_ne_nil mem

/-- For regexes that are match-partial-free, the language of the concatenation
*is* the concatenation of the languages. -/
theorem MatchPartialFree.language_concat {q r : Regex α}
    (qf : q.MatchPartialFree) (rf : r.MatchPartialFree)
    : [/⟨q⟩ ⟨r⟩/].language (fun w ↦ allTerminates_concat qf.1 rf.1 w _ _) =
      q.language (fun w ↦ qf.1 w _ _) * r.language (fun w ↦ rf.1 w _ _) := by
  ext w
  simp only [mem_language_iff, isMatch_concat, Language.mem_mul]
  constructor
  · rintro ⟨mat, qmem, mat', rmem⟩
    have qism := qf.isMatch qmem
    have rism := rf.isMatch rmem.1
    refine ⟨_, qism, _, rism, ?_⟩
    rw [List.extract_append_extract _ (Nat.zero_le _) (monotone _ _ _ _ _ rmem.1), rmem.2]
    simp
  · rintro ⟨wq, qism, wr, rism, app⟩
    have ⟨qmat, qmem⟩ := List.exists_mem_of_ne_nil _ qism
    have ⟨rmat, rmem⟩ := List.exists_mem_of_ne_nil _ rism
    rw [mem_match'_iff] at qmem rmem
    have ⟨qcap₁', qmem₁⟩ := qf.2 _ _ _ _ qmem.1 [] wr 0
    have ⟨rcap₁', rmem₁⟩ := rf.2 _ _ _ _ rmem.1 wq [] qcap₁'
    simp only [qmem.2, and_true, rmem.2, List.extract_eq_drop_take, tsub_zero, List.drop_zero,
      List.take_length, List.nil_append, List.length_nil, List.append_nil,
      Prod.exists, exists_and_right, exists_eq_right, app] at *
    exact ⟨_, _, qmem₁, _, rmem₁⟩

/-- For regexes that are match-partial-free, the language of the star
*is* the star of the language. -/
theorem MatchPartialFree.language_star {t : StarType} {r : Regex α}
    (rf : r.MatchPartialFree)
    : [/⟨r⟩*‹t›/].language (fun w ↦ allTerminates_star rf.1 w _ _) =
      KStar.kstar (r.language (fun w ↦ rf.1 w _ _)) := by
  ext w
  rw [mem_language_iff, isMatch_star_iff_greedy]
  induction h : w.length using Nat.strongRec generalizing w with | ind n ind =>
    cases w with
    | nil =>
      simp only [isMatch_star, List.length_nil, Prod.exists, exists_and_right, exists_eq_right,
        true_or, Language.mem_kstar, List.nil_eq, List.flatten_eq_nil_iff, true_iff]
      use []; simp
    | cons w ws =>
      simp only [isMatch_star, reduceCtorEq, List.length_cons, Prod.exists, exists_and_right,
        exists_eq_right, false_or]
      simp only [← h, List.length_cons, Order.lt_add_one_iff] at ind
      rw [Language.mem_kstar_iff_rec]
      constructor
      · rintro ⟨s, cap, mem, zlt, cap', mem'⟩
        have ism' := (matchPartialFree_star_greedy rf).isMatch mem'
        specialize ind ((w :: ws).extract s (ws.length + 1, cap').1).length _
        · simp only [List.extract_eq_drop_take, List.length_take, List.length_drop]
          simp only [List.length_cons, min_self, tsub_le_iff_right, add_le_add_iff_left]
          linarith
        have ind := (ind _ rfl).mp ism'
        have ism := rf.isMatch mem
        have ism := (mem_language_iff (term := fun w ↦ rf.1 w _ _)).mpr ism
        simp only [reduceCtorEq, ne_eq, false_or]
        rw [← List.length_cons (a := w)] at mem' ind
        use (w :: ws).extract 0 s, (w :: ws).extract s (w :: ws).length
        rw [List.extract_append_extract _ (Nat.zero_le _) (monotone _ _ _ _ _ mem')]
        refine ⟨by simp, by (suffices s ≠ 0 by simpa); exact Nat.pos_iff_ne_zero.mp zlt, ?_⟩
        exact ⟨ism, ind⟩
      · rintro (wat | ⟨a, b, weq, nemp, ism, star⟩) <;> try simp at wat
        rw [mem_language_iff] at ism
        have ⟨mat, mem⟩ := List.exists_mem_of_ne_nil _ ism
        rw [mem_match'_iff] at mem
        have ⟨cap₁', mem₁⟩ := rf.2 _ _ _ _ mem.1 [] ((w :: ws).extract a.length) 0
        simp only [mem.2, List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_length,
          List.nil_append, weq, List.length_append, add_tsub_cancel_left, List.drop_left',
          List.length_nil] at mem₁
        rw! [← weq] at mem₁
        use a.length, cap₁', mem₁, (List.length_pos_of_ne_nil nemp)
        specialize ind b.length _
        · apply congrArg List.length at weq
          simp only [List.length_cons, List.length_append] at weq
          rw [← List.length_pos_iff_ne_nil] at nemp
          linarith
        have ism := (ind b rfl).mpr star
        have ⟨mat, mem⟩ := List.exists_mem_of_ne_nil _ ism
        rw [mem_match'_iff] at mem
        have ⟨cap₁'', mem₁⟩ := (matchPartialFree_star_greedy rf).2 _ _ _ _ mem.1 a [] cap₁'
        simp only [mem.2, List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_length,
          ← weq, List.append_nil, List.length_cons] at mem₁
        exact ⟨_, mem₁⟩

/-! Now to prove that the classic regular operators are actually regular -/

omit deq in
theorem CRegular.cTerminates {r : Regex α} (hr : r.CRegular)
    : r.CTerminates := by
  induction hr with
  | bot => exact CTerminates.bot
  | empty => exact CTerminates.empty
  | unit _ => exact CTerminates.unit _
  | concat _ _ _ _ qt rt => exact CTerminates.concat _ _ qt rt
  | or _ _ _ _ qt rt => exact CTerminates.or _ _ qt rt
  | star _ _ _ rt => exact CTerminates.star _ _ rt

theorem CRegular.allTerminates {r : Regex α} (hr : r.CRegular) :
  r.AllTerminates := hr.cTerminates.allTerminates

theorem CRegular.regular {r : Regex α} {hr : r.CRegular}
    : r.Regular (fun w ↦ hr.allTerminates w _ _) := by
  induction hr with
  | bot => use 0; simp [language_bot]
  | empty => use 1; simp [language_empty]; rfl
  | unit c => use .char c; simp [language_unit]
  | concat q r qcr rcr qr rr =>
    have ⟨qreg, qeq⟩ := qr
    have ⟨rreg, req⟩ := rr
    use qreg * rreg
    rw [qcr.matchPartialFree.language_concat rcr.matchPartialFree,
      RegularExpression.matches'_mul, qeq, req]
  | or q r _ _ qr rr =>
    have ⟨qreg, qeq⟩ := qr
    have ⟨rreg, req⟩ := rr
    use qreg + rreg
    rw [language_or, RegularExpression.matches'_add, qeq, req]
  | star t r rcr rr =>
    have ⟨rreg, req⟩ := rr
    use .star rreg
    rw [rcr.matchPartialFree.language_star, RegularExpression.matches'_star, req]

end Regex
