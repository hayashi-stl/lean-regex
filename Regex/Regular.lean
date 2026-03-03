import Regex.Lemmas.Equiv
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
inductive CRegular : Regex α → Type u where
  | bot : CRegular bot
  | empty : CRegular empty
  | unit c : CRegular (unit c)
  | concat {q} {r} : CRegular q → CRegular r → CRegular (concat q r)
  | or {q} {r} : CRegular q → CRegular r → CRegular (or q r)
  | star {r} : CRegular r → CRegular (star r)

/-- A regex where `partialMatch` does not care about outside context
like captures.
Proving/using a tailored termination condition has proved to be difficult,
so this predicate requires the regex to always terminate. -/
def MatchPartialFree (r : Regex α) :=
  ∃ term : r.AllTerminates,
  ∀ w s cap mat, mat ∈ r.matchPartial w s cap (term w s cap) →
    ∀ (wa wb : List α), ∃ (w' : List α) (weq : w' = wa ++ w.extract s mat.1 ++ wb),
      ∀ cap₁, ∃ cap₁', (⟨(wa ++ w.extract s mat.1).length, by simp [weq]⟩, cap₁') ∈
        r.matchPartial w' ⟨wa.length, by simp [weq]⟩ cap₁ (term _ _ _)

/-- A variant that makes proofs by induction on `s` easier -/
def MatchPartialFree' (r : Regex α) (w : List α) (s : Pos w) :=
  ∃ term : r.AllTerminates,
  ∀ cap mat, mat ∈ r.matchPartial w s cap (term w s cap) →
    ∀ (wa wb : List α), ∃ (w' : List α) (weq : w' = wa ++ w.extract s mat.1 ++ wb),
      ∀ cap₁, ∃ cap₁', (⟨(wa ++ w.extract s mat.1).length, by simp [weq]⟩, cap₁') ∈
        r.matchPartial w' ⟨wa.length, by simp [weq]⟩ cap₁ (term _ _ _)

theorem matchPartialFree_iff_matchPartialFree' {r : Regex α}
    : r.MatchPartialFree ↔ ∀ w s, r.MatchPartialFree' w s := by
  simp only [MatchPartialFree, MatchPartialFree']
  constructor
  · rintro ⟨term, hr⟩ w s
    exact ⟨term, hr w s⟩
  · rintro hr
    by_cases term : r.AllTerminates
    · refine ⟨term, fun w s ↦ ?_⟩
      have ⟨term', hr⟩ := hr w s
      exact hr
    · simp [term] at hr

theorem MatchPartialFree'.cast_iff {r : Regex α} {w : List α} {s : Pos w}
    : r.MatchPartialFree' w s ↔
      ∃ term : r.AllTerminates,
      ∀ cap mat, mat ∈ r.matchPartial w s cap (term w s cap) →
        ∀ (wa wb : List α) (w' : List α) (weq : w' = wa ++ w.extract s mat.1 ++ wb),
          ∀ cap₁, ∃ cap₁', (⟨(wa ++ w.extract s mat.1).length, by simp [weq]⟩, cap₁') ∈
            r.matchPartial w' ⟨wa.length, by simp [weq]⟩ cap₁ (term _ _ _) := by
  constructor
  · rintro ⟨term, hr⟩
    refine ⟨term, fun cap mat mem wa wb w' weq cap₁ ↦ ?_⟩
    have ⟨w'', weq', hr⟩ := hr cap mat mem wa wb
    rw [← weq'] at weq
    have ⟨cap₁', hr⟩ := hr (weq ▸ cap₁)
    use weq ▸ cap₁'
    rw! (castMode := .all) [weq]
    exact hr
  · rintro ⟨term, hr⟩
    refine ⟨term, fun cap mat mem wa wb ↦ ⟨_, rfl, ?_⟩⟩
    exact hr cap mat mem wa wb _ rfl

/-- Casting the theorem so that you can specify what `w'` you want
when using the theorem as well -/
theorem MatchPartialFree.cast {r : Regex α} (hr : r.MatchPartialFree)
    : ∃ term : r.AllTerminates,
      ∀ w s cap mat, mat ∈ r.matchPartial w s cap (term w s cap) →
        ∀ (wa wb w' : List α) (weq : w' = wa ++ w.extract s mat.1 ++ wb),
          ∀ cap₁, ∃ cap₁', (⟨(wa ++ w.extract s mat.1).length, by simp [weq]⟩, cap₁') ∈
            r.matchPartial w' ⟨wa.length, by simp [weq]⟩ cap₁ (term _ _ _) := by
  rcases hr with ⟨term, hr⟩
  refine ⟨term, fun w s cap mat mem wa wb w' weq cap₁ ↦ ?_⟩
  have ⟨w'', weq', hr⟩ := hr w s cap mat mem wa wb
  rw [← weq'] at weq
  have ⟨cap₁', hr⟩ := hr (weq ▸ cap₁)
  use weq ▸ cap₁'
  rw! (castMode := .all) [weq]
  exact hr

theorem matchPartialFree_bot : MatchPartialFree ([/⊥/] : Regex α) := by
  simp [MatchPartialFree, matchPartial_bot, allTerminates_bot]

theorem matchPartialFree_empty : MatchPartialFree ([//] : Regex α) := by
  simp [MatchPartialFree, matchPartial_empty, allTerminates_empty]

theorem matchPartialFree_unit {c : α} : MatchPartialFree [/c/] := by
  simp only [MatchPartialFree, matchPartial_unit, List.mem_dite_nil_right, List.mem_cons,
    List.not_mem_nil, or_false, List.extract_eq_drop_take, List.length_append, List.length_take,
    List.length_drop, Prod.mk.injEq, exists_and_right, exists_eq_right, exists_const,
    List.append_assoc, exists_prop_eq, forall_exists_index, forall_eq_apply_imp_iff,
    Pos.val_succOfIndex, add_tsub_cancel_left, allTerminates_unit]
  intro w s cap wsc wa wb cap₁
  have ⟨slt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
  constructor
  · simp only [← Fin.val_inj, Pos.val_succOfIndex, Nat.add_left_cancel_iff, inf_eq_left]
    refine Nat.le_sub_of_add_le (Nat.one_add_le_iff.mpr slt)
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rw [List.getElem?_append_left (by simp [slt])]
  simp [wsc, Nat.add_one_le_of_lt (Nat.zero_lt_sub_of_lt slt)]

theorem matchPartialFree_concat {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, forall_exists_index, Prod.forall]
  refine ⟨allTerminates_concat qf.1 rf.1, ?_⟩
  intro w s cap s'' cap'' s' cap' qmem rmem wa wb
  have qm := Fin.val_fin_le.mpr (monotone _ _ _ _ _ qmem)
  have rm := Fin.val_fin_le.mpr (monotone _ _ _ _ _ rmem)
  use (wa ++ w.extract ↑s ↑s'' ++ wb), rfl
  intro cap₁
  have qf := qf.cast.2 _ _ _ _ qmem wa (w.extract s' s'' ++ wb)
      (wa ++ w.extract ↑s ↑s'' ++ wb) (by
    rw [eq_comm, ← List.append_assoc, List.append_assoc wa, w.extract_append_extract qm rm])
  have ⟨cap₁', qmem₁⟩ := qf cap₁
  have rf := rf.cast.2 _ _ _ _ rmem (wa ++ w.extract s s') wb
      (wa ++ w.extract ↑s ↑s'' ++ wb) (by
    rw [eq_comm, List.append_assoc wa, w.extract_append_extract qm rm])
  have ⟨cap₁'', rmem₁⟩ := rf cap₁'
  conv at rmem₁ => enter [2, 1]; simp only [List.append_assoc, w.extract_append_extract qm rm]
  exact ⟨_, _, _, qmem₁, rmem₁⟩

theorem matchPartialFree_or {q r : Regex α} (qf : q.MatchPartialFree)
    (rf : r.MatchPartialFree)
    : [/⟨q⟩ | ⟨r⟩/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_or, List.mem_append, Prod.forall]
  refine ⟨allTerminates_or qf.1 rf.1, ?_⟩
  intro w s cap s' cap' mem wa wb
  refine ⟨_, rfl, ?_⟩
  intro cap₁
  rcases mem with mem | mem
  · have ⟨cap₁', mem'⟩ := qf.cast.2 _ _ _ _ mem wa wb _ rfl cap₁
    exact ⟨cap₁', Or.inl mem'⟩
  · have ⟨cap₁', mem'⟩ := rf.cast.2 _ _ _ _ mem wa wb _ rfl cap₁
    exact ⟨cap₁', Or.inr mem'⟩

theorem matchPartialFree_star {r : Regex α} (rf : r.MatchPartialFree)
    : [/⟨r⟩*/].MatchPartialFree := by
  rw [matchPartialFree_iff_matchPartialFree']
  intro w s
  induction s using Pos.strongRecEnd with | ind s ind =>
    refine ⟨allTerminates_star rf.1, ?_⟩
    conv in _ ∈ _ => rw [matchPartial_star]
    conv =>
      enter [2, 2, 2, 2, 2, 1, w', 1, weq, 2, 1, cap₁']
      rw [matchPartial_star]
    simp only [List.mem_append, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
      true_and, List.mem_cons, List.not_mem_nil, or_false,
      exists_prop_eq, Prod.forall, Prod.mk.injEq]
    intro cap s'' cap'' mem wa wb cap₁
    rcases mem with ⟨s', cap', mem, mem'⟩ | eq
    · have rm  := Fin.val_fin_le.mpr (monotone _ _ _ _ _ mem)
      split at mem' <;> rename_i hs
      · have rm' := Fin.val_fin_le.mpr (monotone _ _ _ _ _ mem')
        have rf := rf.cast.2 _ _ _ _ mem wa (w.extract s' s'' ++ wb)
            (wa ++ w.extract ↑s ↑s'' ++ wb) (by
          rw [eq_comm, ← List.append_assoc, List.append_assoc wa, w.extract_append_extract rm rm'])
        have ⟨cap₁', mem₁⟩ := rf cap₁
        have ⟨term, ind⟩ := MatchPartialFree'.cast_iff.mp (ind _ hs)
        specialize ind _ _ mem' (wa ++ w.extract s s') wb
            (wa ++ w.extract ↑s ↑s'' ++ wb) (by
          rw [eq_comm, List.append_assoc wa, w.extract_append_extract rm rm'])
        have ⟨cap₁'', mem₁'⟩ := ind cap₁'
        conv at mem₁' => enter [2, 1]; simp only [List.append_assoc,
          w.extract_append_extract rm rm']
        refine ⟨cap₁'', Or.inl ⟨_, _, mem₁, ?_⟩⟩
        split <;> rename_i hs₁
        · exact mem₁'
        · simp only [List.extract_eq_drop_take, List.length_append, List.length_take,
            List.length_drop, Fin.mk_lt_mk, lt_add_iff_pos_right, lt_inf_iff, tsub_pos_iff_lt,
            Fin.val_fin_lt, not_and, not_lt] at hs₁
          have lt := trans (hs₁ hs) (Fin.val_fin_lt.mpr hs)
          exact ((not_lt.mpr s'.is_le) lt).elim
      · rw [not_lt, ← Fin.val_fin_le] at hs
        have eq := le_antisymm rm hs
        simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem'
        simp [eq, mem']
    · refine ⟨cap₁, Or.inr ?_⟩
      simp [eq]

theorem matchPartialFree_capture {n : ℕ} {r : Regex α} (rf : r.MatchPartialFree)
    : [/(n ← ⟨r⟩)/].MatchPartialFree := by
  simp only [MatchPartialFree, matchPartial_capture, List.mem_map]
  refine ⟨allTerminates_capture rf.1, ?_⟩
  refine fun w s cap mat ⟨cap', mem, up⟩ wa wb ↦ ?_
  simp only [Prod.eq_iff_fst_eq_snd_eq] at up
  refine ⟨wa ++ w.extract ↑s ↑cap'.1 ++ wb, by simp [up.1], fun cap₁ ↦ ?_⟩
  have ⟨cap₁', mem⟩ := rf.cast.2 _ _ _ _ mem wa wb _ rfl cap₁
  refine ⟨_, _, mem, by
    rw [Prod.eq_iff_fst_eq_snd_eq]; simp only [up.1, true_and]; exact rfl⟩

theorem MatchPartialFree.match'_ne_nil {r : Regex α} (rf : r.MatchPartialFree)
    {w} {s} {cap} {mat} (mem : mat ∈ r.matchPartial w s cap (rf.1 w s cap))
    : r.match' (w.extract s mat.1) (rf.1 _ _ _) ≠ [] := by
  have ⟨cap₁', rf⟩ := rf.cast.2 _ _ _ _ mem [] [] (w.extract s mat.1) (by simp) 0
  simp only [List.nil_append, List.length_nil] at rf
  apply List.ne_nil_of_mem
  rw [mem_match'_iff_length_mem]
  exact rf

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
    rw [Fin.val_zero]
    rw [List.extract_append_extract _ (Nat.zero_le _) (monotone _ _ _ _ _ rmem.1), rmem.2]
    simp
  · rintro ⟨wq, qism, wr, rism, app⟩
    have ⟨qmat, qmem⟩ := List.exists_mem_of_ne_nil _ qism
    have ⟨rmat, rmem⟩ := List.exists_mem_of_ne_nil _ rism
    rw [mem_match'_iff] at qmem rmem
    have ⟨qcap₁', qmem₁⟩ := qf.cast.2 _ _ _ _ qmem.1 [] wr w (by simp [qmem.2, app]) 0
    have ⟨rcap₁', rmem₁⟩ := rf.cast.2 _ _ _ _ rmem.1 wq [] w (by simp [rmem.2, app]) qcap₁'
    simp only [List.length_nil, Fin.zero_eta, Fin.coe_ofNat_eq_mod, Nat.zero_mod, qmem,
      List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_length,
      List.nil_append] at qmem₁
    simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, rmem.2, List.extract_eq_drop_take, tsub_zero,
      List.drop_zero, List.take_length, app] at rmem₁
    exact ⟨_, qmem₁, _, rmem₁, rfl⟩

/-- For regexes that are match-partial-free, the language of the star
*is* the star of the language. -/
theorem MatchPartialFree.language_star {r : Regex α}
    (rf : r.MatchPartialFree)
    : [/⟨r⟩*/].language (fun w ↦ allTerminates_star rf.1 w _ _) =
      KStar.kstar (r.language (fun w ↦ rf.1 w _ _)) := by
  ext w
  induction h : w.length using Nat.strongRec generalizing w with | ind n ind =>
    rw [mem_language_iff]
    conv at ind in _ ∈ _ => rw [mem_language_iff]
    cases w with
    | nil =>
      simp only [isMatch_star, List.length_nil, Prod.exists, exists_and_right,
        true_or, Language.mem_kstar, List.nil_eq, List.flatten_eq_nil_iff, true_iff]
      use []; simp
    | cons w ws =>
      simp only [isMatch_star, reduceCtorEq, List.length_cons, Prod.exists, exists_and_right,
        false_or]
      simp only [← h, List.length_cons, Order.lt_add_one_iff] at ind
      rw [Language.mem_kstar_iff_rec]
      constructor
      · rintro ⟨s, cap, mem, zlt, mat', ⟨cap', mem'⟩, eq⟩
        rw [← Fin.val_fin_lt, Fin.val_zero] at zlt
        have ism' := (matchPartialFree_star rf).isMatch mem'
        rw [eq] at ism'
        rw [show mat' = ⟨(w :: ws).length, by simp⟩ by simp [eq, ← Fin.val_inj]] at mem'
        specialize ind ((w :: ws).extract s (ws.length + 1, cap').1).length _
        · simp only [List.extract_eq_drop_take, List.length_take, List.length_drop]
          simp only [List.length_cons, min_self, tsub_le_iff_right, add_le_add_iff_left]
          linarith
        have ind := (ind _ rfl).mp ism'
        have ism := rf.isMatch mem
        have ism := (mem_language_iff (term := fun w ↦ rf.1 w _ _)).mpr ism
        simp only [reduceCtorEq, ne_eq, false_or]
        rw (occs := [2]) [← List.length_cons (a := w)] at ind
        use (w :: ws).extract 0 s, (w :: ws).extract s (w :: ws).length
        rw [List.extract_append_extract _ (Nat.zero_le _) (monotone _ _ _ _ _ mem')]
        refine ⟨by simp, by (suffices s.val ≠ 0 by simpa); exact Nat.pos_iff_ne_zero.mp zlt, ?_⟩
        exact ⟨ism, ind⟩
      · rintro (wat | ⟨a, b, weq, nemp, ism, star⟩) <;> try simp at wat
        rw [mem_language_iff] at ism
        have ⟨mat, mem⟩ := List.exists_mem_of_ne_nil _ ism
        rw [mem_match'_iff] at mem
        have ⟨cap₁', mem₁⟩ := rf.cast.2 _ _ _ _ mem.1 [] ((w :: ws).extract a.length)
          (w :: ws) (by simp [mem.2, weq]) 0
        simp only [List.length_cons, List.length_nil, Fin.zero_eta, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, mem.2, List.extract_eq_drop_take, tsub_zero, List.drop_zero,
          List.take_length, List.nil_append] at mem₁
        refine ⟨_, _, mem₁, (List.length_pos_of_ne_nil nemp), ?_⟩
        specialize ind b.length _
        · apply congrArg List.length at weq
          simp only [List.length_cons, List.length_append] at weq
          rw [← List.length_pos_iff_ne_nil] at nemp
          linarith
        have ism := (ind b rfl).mpr star
        have ⟨mat, mem⟩ := List.exists_mem_of_ne_nil _ ism
        rw [mem_match'_iff] at mem
        have ⟨cap₁'', mem₁⟩ := (matchPartialFree_star rf).cast.2 _ _ _ _ mem.1 a []
          (w :: ws) (by simp [mem.2, weq]) cap₁'
        simp only [List.length_cons, Fin.coe_ofNat_eq_mod, Nat.zero_mod, mem.2,
          List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_length, ← weq] at mem₁
        exact ⟨_, ⟨_, mem₁⟩, by simp⟩

/-! Now to prove that the classic regular operators are actually regular -/

/-- A class of regexes that can be proven to be matchPartialFree -/
inductive CMatchPartialFree : Regex α → Type u where
  | bot : CMatchPartialFree bot
  | empty : CMatchPartialFree empty
  | unit c : CMatchPartialFree (unit c)
  | concat {q} {r} : CMatchPartialFree q → CMatchPartialFree r → CMatchPartialFree (concat q r)
  | or {q} {r} : CMatchPartialFree q → CMatchPartialFree r → CMatchPartialFree (or q r)
  | star {r} : CMatchPartialFree r → CMatchPartialFree (star r)
  | capture n {r} : CMatchPartialFree r → CMatchPartialFree (capture n r)

def CRegular.cMatchPartialFree {r : Regex α} (hr : r.CRegular)
    : r.CMatchPartialFree := match hr with
  | bot => .bot
  | empty => .empty
  | unit c => .unit c
  | concat qind rind => .concat qind.cMatchPartialFree rind.cMatchPartialFree
  | or qind rind => .or qind.cMatchPartialFree rind.cMatchPartialFree
  | star rind => .star rind.cMatchPartialFree

/-- The classic regular operators are match-partial-free. -/
theorem CMatchPartialFree.matchPartialFree {r : Regex α} (hr : r.CMatchPartialFree)
    : r.MatchPartialFree := by
  induction hr with
  | bot => exact matchPartialFree_bot
  | empty => exact matchPartialFree_empty
  | unit _ => exact matchPartialFree_unit
  | concat _ _ qind rind => exact matchPartialFree_concat qind rind
  | or _ _ qind rind => exact matchPartialFree_or qind rind
  | star _ rind => exact matchPartialFree_star rind
  | capture n _ rind => exact matchPartialFree_capture rind

def CMatchPartialFree.cTerminates {r : Regex α} (hr : r.CMatchPartialFree)
    : r.CTerminates := match hr with
  | bot => CTerminates.bot
  | empty => CTerminates.empty
  | unit _ => CTerminates.unit _
  | concat qt rt => CTerminates.concat qt.cTerminates rt.cTerminates
  | or qt rt => CTerminates.or qt.cTerminates rt.cTerminates
  | star rt => CTerminates.star rt.cTerminates
  | capture n rt => CTerminates.capture n rt.cTerminates

theorem CMatchPartialFree.allTerminates {r : Regex α} (hr : r.CMatchPartialFree) :
  r.AllTerminates := hr.cTerminates.allTerminates

theorem CMatchPartialFree.regular {r : Regex α} {hr : r.CMatchPartialFree}
    : r.Regular (fun w ↦ hr.allTerminates w _ _) := by
  induction hr with
  | bot => use 0; simp [language_bot]
  | empty => use 1; simp [language_empty]; rfl
  | unit c => use .char c; simp [language_unit]
  | concat qcr rcr qr rr =>
    have ⟨qreg, qeq⟩ := qr
    have ⟨rreg, req⟩ := rr
    use qreg * rreg
    rw [qcr.matchPartialFree.language_concat rcr.matchPartialFree,
      RegularExpression.matches'_mul, qeq, req]
  | or _ _ qr rr =>
    have ⟨qreg, qeq⟩ := qr
    have ⟨rreg, req⟩ := rr
    use qreg + rreg
    rw [language_or, RegularExpression.matches'_add, qeq, req]
  | star rcr rr =>
    have ⟨rreg, req⟩ := rr
    use .star rreg
    rw [rcr.matchPartialFree.language_star, RegularExpression.matches'_star, req]
  | capture n rcr rr => have ⟨rreg, req⟩ := rr; use rreg; rw [language_capture, req]

/-- A minimal class of regular expressions -/
inductive CMinimalRegular : Regex α → Type u where
  | bot : CMinimalRegular bot
  | unit c : CMinimalRegular (unit c)
  | concat {q} {r} : CMinimalRegular q → CMinimalRegular r → CMinimalRegular (concat q r)
  | or {q} {r} : CMinimalRegular q → CMinimalRegular r → CMinimalRegular (or q r)
  | star {r} : CMinimalRegular r → CMinimalRegular (star r)

def CMinimalRegular.cRegular {r : Regex α} (hr : r.CMinimalRegular)
    : r.CMatchPartialFree := match hr with
  | bot => .bot
  | unit c => .unit c
  | concat qind rind => .concat qind.cRegular rind.cRegular
  | or qind rind => .or qind.cRegular rind.cRegular
  | star rind => .star rind.cRegular

theorem CMinimalRegular.allTerminates {r : Regex α} (hr : r.CMinimalRegular)
    : r.AllTerminates := hr.cRegular.allTerminates

theorem CMinimalRegular.matchPartialFree {r : Regex α} (hr : r.CMinimalRegular)
    : r.MatchPartialFree := hr.cRegular.matchPartialFree

/-- The operations `bot`, `unit`, `concat`, `or`, `star` are powerful enough
to represent all regular languages -/
theorem regular_iff_cMinimalRegular (l : Language α)
    : (∃ r : RegularExpression α, r.matches' = l) ↔
      ∃ r : Regex α, ∃ hr : r.CMinimalRegular,
        r.language (fun w ↦ hr.allTerminates w _ _) = l := by
  constructor
  · intro ⟨r, lan⟩
    induction r generalizing l with
    | zero => refine ⟨_, CMinimalRegular.bot, ?_⟩; simp [← lan, language_bot]
    | epsilon =>
      refine ⟨_, CMinimalRegular.star CMinimalRegular.bot, ?_⟩
      rw [MatchPartialFree.language_star matchPartialFree_bot]
      simp [← lan, language_bot]
    | char c =>
      refine ⟨_, CMinimalRegular.unit c, ?_⟩
      simp [← lan, language_unit]
    | comp q r qind rind =>
      have ⟨q', q'mr, q'l⟩ := qind q.matches' rfl
      have ⟨r', r'mr, r'l⟩ := rind r.matches' rfl
      refine ⟨_, CMinimalRegular.concat q'mr r'mr, ?_⟩
      rw [MatchPartialFree.language_concat q'mr.matchPartialFree r'mr.matchPartialFree]
      simp [← lan, q'l, r'l]
    | plus q r qind rind =>
      have ⟨q', q'mr, q'l⟩ := qind q.matches' rfl
      have ⟨r', r'mr, r'l⟩ := rind r.matches' rfl
      refine ⟨_, CMinimalRegular.or q'mr r'mr, ?_⟩
      simp [language_or, ← lan, q'l, r'l]
    | star r rind =>
      have ⟨r', r'mr, r'l⟩ := rind r.matches' rfl
      refine ⟨_, CMinimalRegular.star r'mr, ?_⟩
      rw [MatchPartialFree.language_star r'mr.matchPartialFree]
      simp [← lan, r'l]
  · intro ⟨r, reg, lan⟩
    have ⟨r', eq⟩ := reg.cRegular.regular
    exact ⟨r', eq ▸ lan⟩

end Regex
