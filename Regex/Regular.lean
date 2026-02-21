import Regex.Basic

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace Regex

/-- Whether a language is truly regular or just a faker. This is
why it's good to separate `Regex` from `RegularExpression`. -/
def isRegular (r : Regex α) := ∃ r' : RegularExpression α, r.language = r'.matches'

/-- A description of regular languages by which
features a regex is allowed to contain -/
inductive limitRegular : Regex α → Prop where
  | bot : limitRegular bot
  | empty : limitRegular empty
  | unit c : limitRegular (unit c)
  | concat q r : limitRegular q → limitRegular r → limitRegular (concat q r)
  | or q r : limitRegular q → limitRegular r → limitRegular (or q r)
  | star t r : limitRegular r → limitRegular (star t r)
  | capture n r : limitRegular r → limitRegular (capture n r)
  -- note: no backref!

section MatchPartialShrink

variable {s : Pos w} {cap : Captures w} {t : IccFrom s} {a : IccTo s} {b : IccFrom t}

/-- A regex where `partialMatch` is basically equivalent to matching
just a part of the sequence. Information like captures is irrelevant. -/
def matchPartialShrink (r : Regex α) :=
  ∀ (w : List α) (s : Pos w) (cap : Captures w) (t : IccFrom s)
      (a : IccTo s) (b : IccFrom t) (capₑ : Captures (w.extract a.val b.val)),
    t ∈ (r.matchPartial w s cap).map Prod.fst ↔
    (s.extract t a b).2 ∈
      (r.matchPartial (w.extract a.val b.val) (s.extract t a b).1 capₑ).map Prod.fst

theorem matchPartialIsMatch_bot
    : matchPartialShrink ([/⊥/] : Regex α) := by
  simp [matchPartialShrink, matchPartial_bot]

theorem matchPartialIsMatch_empty
    : matchPartialShrink ([//] : Regex α) := by
  simp only [matchPartialShrink, List.extract_eq_drop_take, matchPartial_empty,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, forall_const]
  simp only [← Icc.val_inj, Icc.iccFrom_val, Icc.extract_fst_val, Icc.extract_snd_val]
  intro w s t a b
  rw [Nat.sub_eq_iff_eq_add (le_trans a.is_le t.is_ge)]
  rw [Nat.sub_add_cancel a.is_le]

theorem matchPartialIsMatch_unit (c : α)
    : matchPartialShrink [/c/] := by
  simp only [matchPartialShrink, List.extract_eq_drop_take, matchPartial, List.pure_def,
    List.mem_map, Prod.exists, exists_and_right, exists_eq_right, Icc.extract_fst_val]
  intro w s cap t a b capₛ
  split_ifs <;> simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
    exists_eq_right, failure, exists_const, iff_false, Prod.mk.injEq, false_iff,
    ← Icc.val_inj, Icc.extract_fst_val, Icc.extract_snd_val, Icc.succOfIndex_val]
  · rw [Nat.sub_eq_iff_eq_add (le_trans a.is_le t.is_ge), Nat.add_right_comm]
    rw [Nat.sub_add_cancel a.is_le]
  case' pos => rename_i wsc' wsc
  case' neg => rename_i wsc wsc'
  all_goals (
    contrapose! wsc'
    rw [← wsc, List.getElem?_take_of_lt, List.getElem?_drop, Nat.add_sub_cancel' a.is_le]
    apply Nat.sub_lt_sub_right a.is_le
    simp only [Nat.lt_iff_add_one_le]
  )
  · simp only [← wsc']; exact b.is_ge
  · rw [Nat.sub_eq_iff_eq_add (le_trans a.is_le t.is_ge),
      Nat.add_right_comm, Nat.sub_add_cancel a.is_le] at wsc'
    simp only [← wsc']; exact b.is_ge

theorem exists_congr' {α β : Type*} {p : α → Prop} {q : β → Prop} (f : α → β)
    : (∀ a : α, p a ↔ q (f a)) → (∀ b : β, (∀ a : α, f a ≠ b) → ¬q b) →
      ((∃ a : α, p a) ↔ ∃ b : β, q b) := by
  intro alla noa
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨f a, (alla a).mp ha⟩
  · rintro ⟨b, hb⟩
    specialize noa b
    rw [imp_not_comm] at noa
    push_neg at noa
    obtain ⟨a, ha⟩ := noa hb
    exact ⟨a, (alla a).mpr (ha ▸ hb)⟩

theorem matchPartial_subst {s sₑ : Pos w} {cap : Captures w} {t : IccFrom s}
    {cap' : Captures w} (hs : s = sₑ)
    : ((t, cap') ∈ r.matchPartial w s cap) =
      ((⟨t.val, hs ▸ t.property⟩, cap') ∈ r.matchPartial w sₑ cap) := by
  congr
  rw [Subtype.heq_iff_coe_eq]
  simp [hs]

omit deq in
theorem iccFrom_extract_fst_le (s' : IccFrom (s.extract t a b).fst)
    : s.val ≤ s'.val + a.val ∧ s'.val + a.val ≤ b.val := by
  have ab : a.val ≤ b.val := .trans a.is_le <| .trans t.is_ge b.is_ge
  constructor
  · have s'ge := s'.is_ge
    simp only [List.extract_eq_drop_take, Icc.extract_fst_val, tsub_le_iff_right] at s'ge
    exact s'ge
  · have s'le := s'.is_le
    simp only [List.length_extract_nat' ab, b.is_le] at s'le
    rw [Nat.le_sub_iff_add_le ab] at s'le
    exact s'le

omit deq in
theorem iccFrom_extract_fst_le_length (s' : IccFrom (s.extract t a b).fst)
    : s.val ≤ s'.val + a.val ∧ s'.val + a.val ≤ w.length := by
  obtain ⟨lt, rt⟩ := iccFrom_extract_fst_le s'
  exact ⟨lt, .trans rt b.is_le⟩

omit deq in
theorem iccFrom_extract_fst_le_length' (s' : IccFrom (s.extract t a b).fst)
    : 0 ≤ s'.val + a.val ∧ s'.val + a.val ≤ w.length := by
  obtain ⟨lt, rt⟩ := iccFrom_extract_fst_le s'
  exact ⟨.trans (Nat.zero_le _) lt, .trans rt b.is_le⟩

omit deq in
theorem icc_extract_le_sub (a : IccTo s) (b : IccFrom t) {s' : IccFrom s}
    (hs' : s'.val ≤ b.val)
    : (s.extract t a b).fst.val ≤ s'.val - a.val ∧
      s'.val - a.val ≤ (w.extract a.val b.val).length := by
  simp only [List.extract_eq_drop_take, Icc.extract_fst_val, tsub_le_iff_right,
    List.length_take, List.length_drop, le_inf_iff]
  rw [Nat.sub_add_cancel (.trans a.is_le s'.is_ge)]
  rw [Nat.sub_add_cancel (.trans a.is_le <| .trans t.is_ge b.is_ge),
    Nat.sub_add_cancel (.trans a.is_le s.is_le)]
  exact ⟨s'.is_ge, hs', s'.is_le⟩

omit deq in
theorem icc_extract_ne {sₑ' : IccFrom (s.extract t a b).fst}
    {sₑ''' : IccFrom (s.extract t a b).fst} (hsₑ : sₑ'''.val < sₑ'.val)
    : (∀ sₑ'' : IccFrom sₑ', sₑ'''.val ≠ sₑ''.val) ∧
      (∀ s'' : IccFrom (⟨sₑ'.val + a.val, iccFrom_extract_fst_le_length sₑ'⟩ : IccFrom s),
        sₑ'''.val + a.val ≠ s''.val) := by
  have ne := (fun sₑ'' : IccFrom sₑ' ↦ Icc.ne_of_lt_of_mem_iccFrom sₑ'' hsₑ)
  refine ⟨ne, ?_⟩
  intro s''
  contrapose! ne
  refine ⟨⟨s''.val - a.val, ?_⟩, ?_⟩
  · have sₑ'''le := ne ▸ iccFrom_extract_fst_le sₑ'''
    constructor
    · exact Nat.le_sub_of_add_le s''.is_ge
    · simp only [List.length_extract_nat' (.trans a.is_le <| .trans t.is_ge b.is_ge) b.is_le]
      rw [Nat.sub_le_sub_iff_right (.trans a.is_le <| .trans t.is_ge b.is_ge)]
      exact sₑ'''le.right
  simp only []
  exact Nat.eq_sub_of_add_eq ne

theorem matchPartialIsMatch_concat (q r : Regex α)
    : matchPartialShrink q → matchPartialShrink r → matchPartialShrink (concat q r) := by
  intro qm rm
  simp only [matchPartialShrink, matchPartial,
    Icc.iccFrom_expandZero, List.pure_def, List.bind_eq_flatMap, List.mem_map,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Prod.exists,
    ← Icc.val_inj, Prod.mk.injEq, Icc.widenLeft_val, exists_eq_right_right',
    exists_and_right, Icc.extract_fst_val, Icc.extract_snd_val]
  intro w s cap t a b capₑ
  simp only [matchPartialShrink, List.mem_map, Prod.exists,
    exists_and_right, exists_eq_right] at qm rm
  symm
  have ab : a.val ≤ b.val := .trans a.is_le <| .trans t.is_ge b.is_ge
  apply exists_congr' (fun s' ↦ ⟨s'.val + a.val, iccFrom_extract_fst_le_length s'⟩)
  rotate_right 1
  · push_neg
    rintro s''' nos''' ⟨cap'', s', cap', memq, s'', memr, s'''s''⟩
    contrapose! nos'''
    symm at s'''s''
    refine ⟨⟨s'''.val - a.val, icc_extract_le_sub a b (trans nos''' b.is_ge)⟩, ?_⟩
    simp only [← Icc.val_inj]
    rw [Nat.sub_add_cancel (.trans a.is_le <| .trans s'.is_ge <| trans s''.is_ge s'''s'')]
  intro sₑ'''
  refine and_congr ?_ ?_; rotate_left 1
  · simp only []
    rw [eq_tsub_iff_add_eq_of_le (.trans a.is_le t.is_ge)]
  rw [exists_comm]
  conv_rhs => rw [exists_comm]
  apply exists_congr' (fun s₂' ↦ ⟨s₂'.val + a.val, iccFrom_extract_fst_le_length s₂'⟩)
  rotate_right 1
  · push_neg
    intro s' nos' cap'' cap' memq s'' rmem
    contrapose! nos'
    refine ⟨⟨s'.val - a.val, icc_extract_le_sub a b ?_⟩, by
      simp only [← Icc.val_inj]
      rw [Nat.sub_add_cancel (.trans a.is_le s'.is_ge)]⟩
    obtain ⟨sₑ'''ge, sₑ'''le⟩ := iccFrom_extract_fst_le sₑ'''
    simp only [Icc.extract_fst_val] at nos'
    exact .trans s''.is_ge <| trans (symm nos') sₑ'''le
  intro sₑ'
  let s' : IccFrom s := ⟨sₑ'.val + a.val, iccFrom_extract_fst_le_length sₑ'⟩
  by_cases! sₑlt : sₑ'''.val < sₑ'.val
  · obtain ⟨ne, ne'⟩ := icc_extract_ne sₑlt
    simp [ne, ne']
  let s''' : IccFrom (s'.expandZero) := ⟨sₑ'''.val + a.val, by
    have le := iccFrom_extract_fst_le_length sₑ'''
    simp only [Icc.expandZero_val, s']
    exact ⟨Nat.add_le_add_right sₑlt a.val, le.right⟩⟩
  let a' : IccTo (s'.expandZero) := ⟨a.val, ⟨Nat.zero_le _, .trans a.is_le s'.is_ge⟩⟩
  let b' : IccFrom s' := ⟨b.val, ⟨(iccFrom_extract_fst_le sₑ').right, b.is_le⟩⟩
  let b'' : IccFrom s''' := ⟨b.val, ⟨(iccFrom_extract_fst_le sₑ''').right, b.is_le⟩⟩
  specialize qm w s cap s' a b' capₑ
  specialize rm w s'.expandZero
  rw [forall_comm] at rm; specialize rm s'''
  rw [forall_comm] at rm; specialize rm a'
  rw [forall_comm] at rm; specialize rm b''
  simp only [Icc.extract_fst_val, Icc.iccFrom_expandZero, s', b', a', s''', b''] at qm rm
  rw [iff_comm]
  have exeq := s.extract_fst_eq t s' a b b'.is_ge
  simp only [s'] at exeq
  simp only [matchPartial_subst (Eq.symm exeq), Icc.extract_fst_val, Icc.extract_snd_val,
    add_tsub_cancel_right, Subtype.coe_eta] at qm
  have exeq' : (s'.expandZero.extract s''' a' b'').fst = sₑ'.expandZero := by
    simp [← Icc.val_inj, s', a']
  simp only [Icc.extract_fst_val, s', a', s''', b''] at exeq'
  simp only [Icc.extract_fst_val, matchPartial_subst exeq', Icc.iccFrom_expandZero,
    Icc.extract_snd_val, add_tsub_cancel_right] at rm
  constructor
  · rintro ⟨cap'', cap', memq, s'', memr, s'''s''⟩
    obtain ⟨capₑ', memqₑ⟩ := qm.mp ⟨cap', memq⟩
    have s'''s'' : (s''' : IccFrom s') = s'' := by simp [← Icc.val_inj, ← s'''s'', s''']
    simp only [s'''] at s'''s''
    obtain ⟨capₑ'', memrₑ⟩ := (rm cap' capₑ').mp ⟨cap'', s'''s'' ▸ memr⟩
    use capₑ'', capₑ', memqₑ, ?_
  · rintro ⟨capₑ'', capₑ', memqₑ, sₑ'', memrₑ, s'''s''⟩
    obtain ⟨cap', memq⟩ := qm.mpr ⟨capₑ', memqₑ⟩
    simp only [s'''s'', Subtype.coe_eta] at rm
    obtain ⟨cap'', memr⟩ := (rm cap' capₑ').mpr ⟨capₑ'', memrₑ⟩
    refine ⟨cap'', cap', memq, s''', ?_⟩
    simp only [Icc.extract_fst_val, s'''s'', and_true, s''']
    exact memr

theorem matchPartialIsMatch_or (q r : Regex α)
    : matchPartialShrink q → matchPartialShrink r → matchPartialShrink (or q r) := by
  intro qm rm
  simp only [matchPartialShrink, matchPartial, List.map_append, List.mem_append,
    List.mem_map, ← Icc.val_inj, Prod.exists, exists_and_right, Icc.extract_fst_val,
    Icc.extract_snd_val]
  intro w s cap t a b capₑ
  simp only [matchPartialShrink, List.mem_map, Prod.exists,
    exists_and_right, exists_eq_right] at qm rm
  specialize qm w s cap t a b capₑ
  specialize rm w s cap t a b capₑ
  constructor
  · intro or
    rcases or with ⟨s', ⟨cap', mem⟩, s't⟩ | ⟨s', ⟨cap', mem⟩, s't⟩
    case' mp.inl => left
    case' mp.inr => right; revert qm rm; intro rm qm
    case mp.inl | mp.inr =>
      simp only [show s' = t by simp [← Icc.val_inj, s't]] at mem
      obtain ⟨capₑ', memₑ⟩ := qm.mp ⟨cap', mem⟩
      refine ⟨⟨t.val - a.val, icc_extract_le_sub a b b.is_ge⟩,
        ⟨capₑ', memₑ⟩, by simp⟩
  · intro or
    rcases or with ⟨sₑ', ⟨capₑ', memₑ⟩, s't⟩ | ⟨sₑ', ⟨capₑ', memₑ⟩, s't⟩
    case' mpr.inl => left
    case' mpr.inr => right; revert qm rm; intro rm qm
    case mpr.inl | mpr.inr =>
      simp only [show sₑ' = ⟨t.val - a.val, icc_extract_le_sub a b b.is_ge⟩
        by simp [← Icc.val_inj, s't]] at memₑ
      obtain ⟨cap', mem⟩ := qm.mpr ⟨capₑ', memₑ⟩
      exact ⟨t, ⟨cap', mem⟩, rfl⟩

end MatchPartialShrink

def sndErasing {α β γ : Type*} (f : α × β → γ) := ∀ a b₁ b₂, f (a, b₁) = f (a, b₂)

/-- Captures are irrelevant to the internal behavior of `matchPartial` in
regular regexes. -/
theorem limitRegular_matchPartial_eraseCaptures (rlim : limitRegular r)
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
theorem limitRegular_isMatch_concat_star (rlim : limitRegular r) (w : List α)
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

theorem isRegular_limitRegular : limitRegular r → isRegular r := by
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
