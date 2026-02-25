import Regex.Basic
import Regex.Lemmas

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

section MatchPartialShrink

variable {s : Pos w} {cap : Captures w} {t : IccFrom s} {a : IccTo s} {b : IccFrom t}

/-- A regex where `partialMatch` does not care about outside context
like captures -/
def MatchPartialFree (r : Regex α) :=
  ∀ {w : List α} {s : Pos w} {cap : Captures w}
      {term : r.Terminates w s cap} {s' : Pos w} {cap' : Captures w}
      (mem : (s', cap') ∈ r.matchPartial w s cap term)
      (wa : List α) (wb : List α) (cap₁ : Captures (wa ++ w.extract s.val s'.val ++ wb))
      (term₁ : r.Terminates (wa ++ w.extract s.val s'.val ++ wb)
        (s.recycle s s' (monotone mem) wa wb) cap₁),
    ∃ cap₁', (s'.recycle s s' (le_refl _) wa wb, cap₁') ∈
      r.matchPartial (wa ++ w.extract s.val s'.val ++ wb)
        (s.recycle s s' (monotone mem) wa wb) cap₁ term₁

theorem matchPartialFree_bot : MatchPartialFree ([/⊥/] : Regex α) := by
  simp [MatchPartialFree, matchPartial_bot]

theorem matchPartialFree_empty : MatchPartialFree ([//] : Regex α) := by
  simp only [MatchPartialFree, matchPartial_empty, List.mem_cons, Prod.mk.injEq, ← Icc.val_inj,
    List.not_mem_nil, or_false, List.extract_eq_drop_take, Icc.recycle_val, tsub_self, add_zero,
    Nat.add_eq_left, exists_eq_right, forall_and_index]
  intro w s cap term t cap' teq
  simp [teq]

theorem matchPartialFree_unit (c : α) : MatchPartialFree [/c/] := by
  simp only [MatchPartialFree, matchPartial_unit, List.mem_dite_nil_right, List.mem_cons,
    Prod.mk.injEq, ← Icc.val_inj, Icc.succOfIndex_val, List.not_mem_nil, or_false, exists_and_left,
    exists_prop, List.extract_eq_drop_take, List.append_assoc, Icc.recycle_val, tsub_self, add_zero,
    Nat.add_left_cancel_iff, ↓existsAndEq, and_true, forall_and_index]
  intro w s cap term s' cap' s'add wsc capeq wa wb cap₁ term₁
  have ⟨lt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
  have one : 1 ≤ w.length - s.val := by
    by_contra!
    rw [Nat.lt_one_iff, Nat.sub_eq_zero_iff_le] at this
    exact not_le.mpr lt this
  suffices (if s.val < w.length then w[s.val]? else wb[0]?) = some c by
    simpa [s'add, List.getElem?_append]
  rw [Nat.le_sub_iff_add_le' s.is_le, ← Nat.lt_iff_add_one_le] at one
  simp [one, wsc]

theorem matchPartialFree_concat {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, forall_exists_index] at ⊢
  intro w s cap term s'' cap'' s' cap' qmem rmem wa wb cap₁ term₁
  -- Please excuse the massive ▸ spam ahead
  have eaear := List.extract_append_extract_assoc_right (monotone qmem) (monotone rmem) wa wb
  have rear := Icc.recycle_extract_append_right (le_refl s) (monotone qmem) (monotone rmem) wa wb
  have eaeal := List.extract_append_extract_assoc_left (monotone qmem) (monotone rmem) wa wb
  have real := Icc.recycle_extract_append_left (monotone qmem) (monotone rmem) (le_refl s'') wa wb
  -- And the ▸s have gotten slow
  have qf₁ := qf qmem wa (w.extract s'.val s''.val ++ wb)
  simp only [rear] at qf₁
  rw! (castMode := .all) [eaear] at qf₁
  specialize qf₁ cap₁ (concat_terminates.mp term₁).1
  have ⟨cap₁', qf₁⟩ := qf₁
  simp only at qf₁
  have rf₁ := rf rmem (wa ++ w.extract s.val s'.val) wb
  simp only [real] at rf₁
  rw! (castMode := .all) [eaeal] at rf₁
  specialize rf₁ cap₁' (by
    have term' := (concat_terminates.mp term₁).2 _ qf₁
    simp only at term'
    refine cast ?_ term'
    congr 1
    rw [Icc.recycle_extract_append_right (monotone qmem) (le_refl _),
      Icc.recycle_extract_append_left (monotone qmem) (le_refl _)]
    · simp only [List.extract_eq_drop_take, eqRec_eq_cast, cast_cast, cast_eq]
    exact monotone rmem)
  have ⟨cap₁'', rf₁⟩ := rf₁
  simp only at rf₁
  refine ⟨cap₁'', _, _, qf₁, cast ?_ rf₁⟩
  congr 2
  rw [Icc.recycle_extract_append_right (monotone qmem) (le_refl _),
    Icc.recycle_extract_append_left (monotone qmem) (le_refl _)]
  · simp only [List.extract_eq_drop_take, eqRec_eq_cast, cast_cast, cast_eq]
  exact (monotone rmem)

theorem matchPartialFree_or {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ | ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_or, List.mem_append]
  intro w s cap term s' cap' mem wa wb cap₁ term₁
  rcases mem with mem | mem
  · have ⟨cap₁', mem'⟩ := qf mem wa wb cap₁ (or_terminates.mp term₁).1
    exact ⟨cap₁', Or.inl mem'⟩
  · have ⟨cap₁', mem'⟩ := rf mem wa wb cap₁ (or_terminates.mp term₁).2
    exact ⟨cap₁', Or.inr mem'⟩

theorem matchPartialFree_star_greedy {r : Regex α}
    (rf : r.MatchPartialFree)
    : [/⟨r⟩*/].MatchPartialFree := by
  rw [MatchPartialFree]
  simp only [matchPartial_star, star_terminates']
  rw [← MatchPartialFree.eq_1]
  refine matchPartialFree_or (matchPartialFree_or ?_ ?_) matchPartialFree_empty
  ·

end MatchPartialShrink

def sndErasing {α β γ : Type*} (f : α × β → γ) := ∀ a b₁ b₂, f (a, b₁) = f (a, b₂)

/-- Captures are irrelevant to the internal behavior of `matchPartial` in
regular regexes. -/
theorem limitRegular_matchPartial_eraseCaptures (rlim : classRegular r)
    (w : List α) (s : Pos w)
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
    have pur (a : PosFrom s × Captures w)
        : (fun a_1 : PosFrom a.1.pos × Captures w ↦ [f (a.1.widen a_1.1, a_1.2)]) =
          pure ∘ (fun a_1 : PosFrom a.1.pos × Captures w ↦ f (a.1.widen a_1.1, a_1.2)) := by
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
      | concat p q => isMatch r w ↔ ∃ s : Pos w,
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
