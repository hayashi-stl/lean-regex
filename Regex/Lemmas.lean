import Regex.Basic

-- Some useful lemmas about regexes

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w} {term : r.Terminates w s cap}

/-- A partial match is monotone if all matches end on or after where they start.
Ideally this will be true for all regexes. -/
def Monotone (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
    (term : r.Terminates w s cap) :=
    ∀ t ∈ (r.matchPartial w s cap term).map Prod.fst, s ≤ t

theorem monotone_bot : [/⊥/].Monotone w s cap bot_terminates := by
  simp [Monotone, matchPartial_bot]

theorem monotone_empty : [//].Monotone w s cap empty_terminates := by
  simp [Monotone, matchPartial_empty]

theorem monotone_unit {c : α} : [/c/].Monotone w s cap unit_terminates := by
  simp only [Monotone, matchPartial_unit, List.mem_map, List.mem_dite_nil_right,
    List.mem_cons, List.not_mem_nil, or_false, ← Icc.val_inj, Prod.exists,
    Prod.mk.injEq, Icc.succOfIndex_val, exists_and_left, exists_prop, exists_and_right,
    ↓existsAndEq, and_true, forall_exists_index, and_imp]
  intro t s' hs' _
  rw [Icc.val_le_val, hs']
  intro _
  linarith

theorem monotone_concat {q r : Regex α} {term : [/⟨q⟩ ⟨r⟩/].Terminates w s cap}
    (qm : q.Monotone w s cap (concat_terminates.mp term).1)
    (rm : ∀ mat (mem : mat ∈ q.matchPartial w s cap (concat_terminates.mp term).1),
      r.Monotone w mat.1 mat.2 ((concat_terminates.mp term).2 mat mem))
    : [/⟨q⟩ ⟨r⟩/].Monotone w s cap term := by
  simp only [Monotone, List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
    forall_exists_index, Prod.forall, matchPartial_concat, List.map_flatten,
    List.mem_flatten, List.mem_pmap, ↓existsAndEq, true_and] at qm rm ⊢
  exact fun s'' s' cap' qmem cap'' rmem ↦ .trans (qm _ _ qmem) (rm _ _ qmem _ _ rmem)

theorem monotone_or {q r : Regex α} {term : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap}
    (qm : q.Monotone w s cap (or_terminates.mp term).1)
    (rm : r.Monotone w s cap (or_terminates.mp term).2)
    : [/⟨q⟩ | ⟨r⟩/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_or, List.map_append, List.mem_append]
  exact fun s' mem ↦ Or.casesOn mem (fun qmem ↦ qm _ qmem) (fun rmem ↦ rm _ rmem)

theorem monotone_filterEmpty {e : Bool} {r : Regex α}
    {term : [/⟨r⟩ ‹e›ε/].Terminates w s cap}
    (rm : r.Monotone w s cap (filterEmpty_terminates.mp term))
    : [/⟨r⟩ ‹e›ε/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
    Bool.decide_eq_true, List.mem_map, List.mem_filter, beq_iff_eq, Prod.exists, exists_and_right,
    exists_eq_right, forall_exists_index, and_imp] at rm ⊢
  exact fun s' _ mem _ ↦ rm _ _ mem

theorem monotone_star {t : StarType} {r : Regex α} {term : [/⟨r⟩*‹t›/].Terminates w s cap}
    (rm : r.Monotone w s cap (star_terminates.mp term).1)
    (rm' : ∀ mat (mem : mat ∈ r.matchPartial w s cap (star_terminates.mp term).1)
      (slt : s < mat.1),
      [/⟨r⟩*‹t›/].Monotone w mat.1 mat.2 ((star_terminates.mp term).2 mat mem slt))
    : [/⟨r⟩*‹t›/].Monotone w s cap term := by
  simp only [Monotone, List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
    forall_exists_index, Prod.forall] at rm rm' ⊢
  simp only [matchPartial_star]
  cases t
  case greedy | lazy =>
    simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
      matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
      List.append_assoc, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
      List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at ⊢
    intro s'' cap'' or
    try rw [or_comm (a := _ ∧ cap'' = _), or_assoc] at or
    rcases or with mem | ⟨s', cap', rmem, r'mem⟩ | mem
    · exact rm _ _ mem.1
    · exact .trans (rm _ _ rmem.1) (rm' _ _ rmem.1 rmem.2 _ _ r'mem)
    · exact mem.1 ▸ le_refl _

theorem monotone_start : [/⊢/].Monotone w s cap start_terminates := by
  simp [Monotone, matchPartial_start]

theorem monotone_end' : [/⊣/].Monotone w s cap end'_terminates := by
  simp [Monotone, matchPartial_end']

theorem monotone_capture {n : ℕ} {r : Regex α} {term : [/(‹n› ⟨r⟩)/].Terminates w s cap}
    (rm : r.Monotone w s cap (capture_terminates.mp term))
    : [/(‹n› ⟨r⟩)/].Monotone w s cap term := by
  simp only [Monotone, List.mem_map, Prod.exists, exists_and_right, exists_eq_right,
    forall_exists_index, matchPartial_capture, List.map_map, Function.comp_apply] at rm ⊢
  exact rm

--theorem monotone_list {l : List α}
--    : (list l).Monotone w s cap list_terminates := by
--  induction l generalizing s cap with
--  | nil => simp [list, monotone_empty]
--  | cons a as ind =>
--    simp only [list]
--    apply monotone_concat monotone_unit
--    exact fun _ _ ↦ ind

theorem monotone_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].Monotone w s cap backref_terminates := by
  rw [Monotone, matchPartial_backref]
  split
  · split <;> simp
  · simp only [List.extract_eq_drop_take, add_tsub_cancel_left, List.mem_map,
      List.mem_dite_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.exists,
      Prod.mk.injEq, exists_and_right, ↓existsAndEq, and_true, exists_eq_right, forall_exists_index,
      forall_eq_apply_imp_iff]
    conv in _ ≤ _ => rw [Icc.val_le_val, Icc.addOfIndex_val]
    simp

theorem monotone : r.Monotone w s cap term := by
  revert term
  induction s using Icc.strongRecEnd generalizing r cap with | ind s ind =>
    intro term
    induction r generalizing cap with
    | bot => exact monotone_bot
    | empty => exact monotone_empty
    | unit _ => exact monotone_unit
    | concat q r qind rind =>
      refine monotone_concat qind fun mat mem ↦ ?_
      simp only [Monotone, List.mem_map, Prod.exists, exists_and_right,
        exists_eq_right, forall_exists_index] at qind
      rcases lt_or_eq_of_le (qind mat.1 mat.2 mem) with lt | eq
      · exact ind _ lt
      · rw! [← eq]; exact rind
    | or q r qind rind => exact monotone_or qind rind
    | filterEmpty e q qind => exact monotone_filterEmpty qind
    | star t q qind =>
      refine monotone_star qind fun mat mem lt ↦ ?_
      exact ind _ lt
    | start => exact monotone_start
    | end' => exact monotone_end'
    | capture n q qind => exact monotone_capture qind
    | backref _ _ => exact monotone_backref

end Regex
