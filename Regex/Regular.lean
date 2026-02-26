import Regex.Lemmas.Bounds
import Regex.Lemmas.Monotone

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace Regex

/-- Whether a language is truly regular or just a faker. This is
why it's good to separate `Regex` from `RegularExpression`. -/
def isRegular (r : Regex α) (term : ∀ w, r.Terminates w 0 0)
  := ∃ r' : RegularExpression α, r.language term = r'.matches'

/-- The classic regular expression operators -/
inductive classRegular : Regex α → Prop where
  | bot : classRegular bot
  | empty : classRegular empty
  | unit c : classRegular (unit c)
  | concat q r : classRegular q → classRegular r → classRegular (concat q r)
  | or q r : classRegular q → classRegular r → classRegular (or q r)
  | star t r : classRegular r → classRegular (star t r)

section MatchPartialFree

variable {s : ℕ} {cap : Captures}

/-- A regex where `partialMatch` does not care about outside context
like captures -/
def MatchPartialFree (r : Regex α) :=
  ∀ w s cap term mat, mat ∈ r.matchPartial w s cap term →
  ∀ (wa wb : List α) cap₁ term₁,
    ∃ cap₁', ((wa ++ w.extract s mat.1).length, cap₁') ∈
      r.matchPartial (wa ++ w.extract s mat.1 ++ wb) wa.length cap₁ term₁

theorem matchPartialFree_bot : MatchPartialFree ([/⊥/] : Regex α) := by
  simp [MatchPartialFree, matchPartial_bot]

theorem matchPartialFree_empty : MatchPartialFree ([//] : Regex α) := by
  simp [MatchPartialFree, matchPartial_empty]

theorem matchPartialFree_unit (c : α) : MatchPartialFree [/c/] := by
  simp only [MatchPartialFree, matchPartial_unit, List.mem_ite_nil_right, List.mem_cons,
    List.not_mem_nil, or_false, List.extract_eq_drop_take, List.append_assoc, Prod.mk.injEq,
    exists_and_left, ↓existsAndEq, and_true, and_imp,
    forall_eq_apply_imp_iff, add_tsub_cancel_left]
  intro w s cap term wsc wa wb cap₁ term₁
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  have ⟨slt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
  rw [List.getElem?_append_left (by simp [slt])]
  simp [wsc, Nat.add_one_le_of_lt (Nat.zero_lt_sub_of_lt slt)]

theorem matchPartialFree_concat {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, forall_exists_index, Prod.forall]
  intro w s cap term s'' cap'' s' cap' qmem rmem wa wb cap₁ term₁
  specialize qf _ _ _ _ _ qmem wa (w.extract s' s'' ++ wb) cap₁
  have qm := monotone _ _ _ _ _ qmem
  have rm := monotone _ _ _ _ _ rmem
  rw [List.extract_append_extract_assoc_right _ qm rm] at qf
  have ⟨cap₁', qmem₁⟩ := qf (concat_terminates.mp term₁).1
  specialize rf _ _ _ _ _ rmem (wa ++ w.extract s s') wb cap₁'
  rw [List.extract_append_extract_assoc_left _ qm rm] at rf
  have ⟨cap₁'', rmem₁⟩ := rf ((concat_terminates.mp term₁).2 _ qmem₁)
  rw [List.append_assoc _ (w.extract s s'), List.extract_append_extract _ qm rm] at rmem₁
  exact ⟨_, _, _, qmem₁, rmem₁⟩

theorem matchPartialFree_or {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ | ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_or, List.mem_append, Prod.forall]
  intro w s cap term s' cap' mem wa wb cap₁ term₁
  rcases mem with mem | mem
  · have ⟨cap₁', mem'⟩ := qf _ _ _ _ _ mem wa wb cap₁ (or_terminates.mp term₁).1
    exact ⟨cap₁', Or.inl mem'⟩
  · have ⟨cap₁', mem'⟩ := rf _ _ _ _ _ mem wa wb cap₁ (or_terminates.mp term₁).2
    exact ⟨cap₁', Or.inr mem'⟩

theorem matchPartialFree_filterEmpty {e : Bool} {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩ ‹e›ε/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff,
    Bool.decide_iff_dist, Bool.decide_eq_true, List.mem_filter, beq_iff_eq,
    and_imp, Prod.forall]
  intro w s cap term s' cap' mem dec wa wb cap₁ term₁
  have ⟨cap₁', mem₁⟩ := rf _ _ _ _ _ mem _ _ _ (filterEmpty_terminates.mp term₁)
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
  rw [MatchPartialFree]
  simp only [or_terminates_comm (q := r), mem_matchPartial_or_comm (q := r)]
  exact mpf

theorem matchPartialFree_star_greedy {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩*/].MatchPartialFree := by
  intro w s
  by_cases! sle : s ≤ w.length
  · induction s, sle using decreasingStrongRec with | ind s sle ind =>
      simp only [matchPartial_star]
      simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
        matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
        List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
        List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, List.not_mem_nil,
        or_false, Prod.mk.injEq, Prod.forall]
      intro cap term s'' cap'' mem wa wb cap₁ term₁
      rcases mem with (mem | ⟨s', cap', mem, mem'⟩) | eq
      · have ⟨cap₁', mem₁⟩ := rf _ _ _ _ _ mem.1 wa wb cap₁ (star_terminates.mp term₁).1
        refine ⟨_, Or.inl (Or.inl ⟨mem₁, ?_⟩)⟩
        have eq := le_antisymm mem.2 (monotone _ _ _ _ _ mem.1)
        simp [eq]
      · have s'le := endInBounds _ _ sle _ _ _ mem.1
        specialize rf _ _ _ _ _ mem.1 wa (w.extract s' s'' ++ wb) cap₁
        have rm := monotone _ _ _ _ _ mem.1
        have rm' := monotone _ _ _ _ _ mem'
        rw [List.extract_append_extract_assoc_right _ rm rm'] at rf
        have ⟨cap₁', mem₁⟩ := rf (star_terminates.mp term₁).1
        specialize ind s' s'le mem.2 _ _ _ mem' (wa ++ w.extract s s') wb cap₁'
        rw [List.extract_append_extract_assoc_left _ rm rm'] at ind
        have term₁ := (star_terminates.mp term₁).2 _ mem₁ (by
          (suffices s < s' ∧ s < w.length by simpa); exact ⟨mem.2, trans mem.2 s'le⟩)
        have ⟨cap₁'', mem₁'⟩ := ind term₁
        rw [List.append_assoc _ (w.extract s s'), List.extract_append_extract _ rm rm'] at mem₁'
        refine ⟨cap₁'', Or.inl (Or.inr ⟨_, _, ⟨mem₁, ?_⟩, mem₁'⟩)⟩
        suffices s < s' ∧ s < w.length by simpa
        exact ⟨mem.2, trans mem.2 s'le⟩
      · refine ⟨cap₁, Or.inr ?_⟩
        simp [eq]
  · intro cap term mat mem wa wb cap₁ term₁
    have bound := matchPartial_outOfBounds_eq (le_of_lt sle) mem
    use cap₁
    simp [bound, matchPartial_star, matchPartial_or, matchPartial_empty]

theorem matchPartialFree_star_greedy_iff_lazy {r : Regex α}
    : [/⟨r⟩*/].MatchPartialFree ↔ [/⟨r⟩*?/].MatchPartialFree := by
  simp only [MatchPartialFree, star_terminates', matchPartial_star,
    or_terminates_comm (q := [//]), mem_matchPartial_or_comm (q := [//])]
  simp only [or_terminates, matchPartial_or, concat_terminates, matchPartial_concat,
    star_terminates_greedy_iff_lazy, matchPartial_empty]
  simp only [List.mem_append, List.mem_flatten, List.mem_pmap, ↓existsAndEq,
    mem_matchPartial_star_greedy_iff_lazy]

theorem matchPartialFree_star {t : StarType} {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩*‹t›/].MatchPartialFree := by
  cases t with
  | greedy => exact matchPartialFree_star_greedy rf
  | lazy => exact matchPartialFree_star_greedy_iff_lazy.mp (matchPartialFree_star_greedy rf)

end MatchPartialFree

def sndErasing {α β γ : Type*} (f : α × β → γ) := ∀ a b₁ b₂, f (a, b₁) = f (a, b₂)

/-- Captures are irrelevant to the internal behavior of `matchPartial` in
regular regexes. -/
theorem limitRegular_matchPartial_eraseCaptures (rlim : classRegular r)
    (w : List α) (s : ℕ)
    : ∀ {β : Type*} (f : _ → β), sndErasing f → ∀ c₁ c₂,
      (r.matchPartial w s c₁).map f =
      (r.matchPartial w s c₂).map f := by
  simp only [sndErasing]
  induction rlim generalizing s
  · simp [matchPartial_bot]
  · simp only [matchPartial_empty, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact (fun f sf ↦ sf s.posFrom)
  · rename_i c
    simp only [matchPartial, failure, List.pure_def]
    intro β f sf c₁ c₂
    simp [apply_dite (List.map f), sf _ c₁ c₂]
  · rename_i p q plim qlim pind qind
    simp only [matchPartial, List.pure_def, List.bind_eq_flatMap]
    simp only [List.map_flatMap, List.map_cons, List.map_nil]
    intro β f sf c₁ c₂
    have pur (a : PosFrom s × Captures)
        : (fun a_1 : PosFrom a.1.pos × Captures ↦ [f (a.1.widen a_1.1, a_1.2)]) =
          pure ∘ (fun a_1 : PosFrom a.1.pos × Captures ↦ f (a.1.widen a_1.1, a_1.2)) := by
      simp [Function.comp_def, List.pure_def]
    simp only [pur, List.flatMap_pure_eq_map]
    simp only [List.flatMap]
    congr 1
    rw [pind s _ _ c₁ c₂]
    intro s' c₁' c₂'; simp only []
    rw [qind s'.pos _ _ c₁' c₂']
    simp only []
    exact (fun a ↦ sf (s'.widen a))
  · rename_i p q plim qlim pind qind
    simp [matchPartial]
    intros β f sf c₁ c₂
    rw [pind s f sf c₁ c₂, qind s f sf c₁ c₂]
  · rename_i t q qlim qind
    induction w; all_goals (
      simp only [matchPartial.eq_def, List.pure_def, List.cons_append, List.nil_append]
      simp only [matchPartialStar, Prod.mk.eta, List.pure_def, List.map_eq_map,
        List.bind_eq_flatMap]
      intro β f sf c₁ c₂
      rw [StarType.map_match (List.map f), StarType.map_match (List.map f)]
      simp only [List.map_append, List.map_flatMap, List.map_cons, List.map_nil]
    )
    ·
      simp only [Pos.nil_eq, ↓reduceIte, List.map_cons, List.map_nil]
      have pur : (fun a ↦ [f a]) = pure ∘ (fun a ↦ f a) := by simp [Function.comp_def]
      simp [pur, List.flatMap_pure_eq_map, show (fun a ↦ f a) = f by rfl,
        qind s f sf c₁ c₂, sf s.posFrom c₁ c₂]
    expose_names


      --simp [List.flatMap_pure_eq_map]

    --rcases t with laze | greed
    --· simp only [matchPartial, List.pure_def, List.cons_append, List.nil_append,
    --    List.map_cons, List.cons.injEq]
    --  simp only [matchPartial_star, Prod.mk.eta, List.pure_def, List.map_eq_map,
    --    List.bind_eq_flatMap]

/-- If the regex is actually regular, `isMatch` on `concat`
and `star` behave nicely -/
theorem limitRegular_isMatch_concat_star (rlim : classRegular r) (w : List α)
    : match r with
      | concat p q => isMatch r w ↔ ∃ s : ℕ,
          isMatch p (w.take s.val) ∧ isMatch q (w.drop s.val)
      | star t q => isMatch r w ↔ (hw : w ≠ []) →
          ∃ s : PosFrom (Pos.succOfLt (List.length_pos_of_ne_nil hw)),
            isMatch q (w.take s.val) ∧ isMatch r (w.drop s.val)
      | _ => True
      := by
  induction rlim
  case bot | empty | unit | or | capture => simp
  · rename_i p q plim qlim pind qind
    simp only []
    rw [isMatch, match'_concat]
  --intro lim
  --induction lim
  --case bot | empty | unit | or | capture => simp
  --· rename_i p q plim qlim pind qind
  --  simp only [concat.injEq, and_imp, forall_apply_eq_imp_iff, forall_eq',
  --    reduceCtorEq, IsEmpty.forall_iff, implies_true, and_true]
  --  intro w

theorem isRegular_limitRegular : classRegular r → isRegular r := by
  intro lim
  induction lim
  · use 0
    simp [language_bot]
  · use 1
    simp [language_empty]; rfl
  · rename_i c
    use RegularExpression.char c
    simp [language_unit]
  · sorry
  · rename_i q r qlim rlim qreg rreg
    rcases qreg with ⟨q', q'eq⟩
    rcases rreg with ⟨r', r'eq⟩
    use q' + r'
    simp [language_or, q'eq, r'eq]

end Regex
