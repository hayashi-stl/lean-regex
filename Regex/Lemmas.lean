import Regex.Lemmas.Bounds

-- Some useful lemmas about regexes

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : ℕ} {cap : Captures} {term : r.Terminates w s cap}

/-- A partial match is monotone if all matches end on or after where they start.
Ideally this will be true for all regexes. -/
def Monotone (r : Regex α) (w : List α) (s : ℕ) (cap : Captures)
    (term : r.Terminates w s cap) :=
    ∀ {s'} {cap'}, (s', cap') ∈ r.matchPartial w s cap term → s ≤ s'

theorem monotone_bot : [/⊥/].Monotone w s cap bot_terminates := by
  simp [Monotone, matchPartial_bot]

theorem monotone_empty : [//].Monotone w s cap empty_terminates := by
  simp [Monotone, matchPartial_empty]

theorem monotone_unit {c : α} : [/c/].Monotone w s cap unit_terminates := by
  simp only [Monotone, matchPartial_unit, List.mem_ite_nil_right, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false, and_imp]
  intro t s' hs' _ _
  linarith

theorem monotone_concat {q r : Regex α} {term : [/⟨q⟩ ⟨r⟩/].Terminates w s cap}
    (qm : q.Monotone w s cap (concat_terminates.mp term).1)
    (rm : ∀ mat (mem : mat ∈ q.matchPartial w s cap (concat_terminates.mp term).1),
      r.Monotone w mat.1 mat.2 ((concat_terminates.mp term).2 mat mem))
    : [/⟨q⟩ ⟨r⟩/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, forall_exists_index]
  exact fun s' cap' qmem rmem ↦ .trans (qm qmem) (rm _ qmem rmem)

theorem monotone_or {q r : Regex α} {term : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap}
    (qm : q.Monotone w s cap (or_terminates.mp term).1)
    (rm : r.Monotone w s cap (or_terminates.mp term).2)
    : [/⟨q⟩ | ⟨r⟩/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_or, List.mem_append]
  exact fun mem ↦ Or.casesOn mem (fun qmem ↦ qm qmem) (fun rmem ↦ rm rmem)

theorem monotone_filterEmpty {e : Bool} {r : Regex α}
    {term : [/⟨r⟩ ‹e›ε/].Terminates w s cap}
    (rm : r.Monotone w s cap (filterEmpty_terminates.mp term))
    : [/⟨r⟩ ‹e›ε/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
    Bool.decide_eq_true, List.mem_filter, beq_iff_eq, and_imp] at rm ⊢
  exact fun mem _ ↦ rm mem

theorem monotone_star {t : StarType} {r : Regex α} {term : [/⟨r⟩*‹t›/].Terminates w s cap}
    (rm : r.Monotone w s cap (star_terminates.mp term).1)
    (rm' : ∀ mat (mem : mat ∈ r.matchPartial w s cap (star_terminates.mp term).1)
      (slt : s < mat.1),
      [/⟨r⟩*‹t›/].Monotone w mat.1 mat.2 ((star_terminates.mp term).2 mat mem slt))
    : [/⟨r⟩*‹t›/].Monotone w s cap term := by
  simp only [Monotone, Prod.forall] at rm rm' ⊢
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
    · exact rm mem.1
    · exact .trans (rm rmem.1) (rm' _ _ rmem.1 rmem.2 r'mem)
    · exact mem.1 ▸ le_refl _

theorem monotone_start : [/⊢/].Monotone w s cap start_terminates := by
  exact fun mem ↦ by simp [matchPartial_start] at mem; simp [mem.2]

theorem monotone_end' : [/⊣/].Monotone w s cap end'_terminates := by
  exact fun mem ↦ by simp [matchPartial_end'] at mem; simp [mem.2]

theorem monotone_capture {n : ℕ} {r : Regex α} {term : [/(‹n› ⟨r⟩)/].Terminates w s cap}
    (rm : r.Monotone w s cap (capture_terminates.mp term))
    : [/(‹n› ⟨r⟩)/].Monotone w s cap term := by
  simp only [Monotone, matchPartial_capture, List.mem_map, Prod.mk.injEq, Prod.exists, ↓existsAndEq,
    true_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun cap ↦ rm

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
  split <;> expose_names
  · split <;> simp
  · simp only [List.extract_eq_drop_take, List.length_take, List.length_drop, add_tsub_cancel_left,
      List.mem_ite_nil_right, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_imp]
    intro _ _ _ seq _
    simp [seq]

theorem monotone : r.Monotone w s cap term := by
  --by_cases! h : s ≤ w.length (by_cases unfolds Monotone and `intro`s variables :( )
  rcases le_or_gt s w.length with h | h
  · revert term
    induction s, h using decreasingStrongRec generalizing r cap with | ind s slt ind =>
      intro term
      induction r generalizing cap with
      | bot => exact monotone_bot
      | empty => exact monotone_empty
      | unit _ => exact monotone_unit
      | concat q r qind rind =>
        refine monotone_concat qind fun mat mem ↦ ?_
        simp only [Monotone] at qind
        rcases lt_or_eq_of_le (qind mem) with lt | eq
        · exact ind mat.1 slt _ lt
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
