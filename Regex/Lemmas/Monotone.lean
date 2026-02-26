import Regex.Lemmas.Bounds

/-! Here we prove monotonicity of regex matches. A regex match does not
end before it starts. -/

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : ℕ} {cap : Captures} {term : r.Terminates w s cap}

/-- Regexes where matches don't end before they start (all the regexes) -/
def Monotone (r : Regex α) :=
    ∀ w s cap (term : r.Terminates w s cap)
    mat, mat ∈ r.matchPartial w s cap term → s ≤ mat.1

theorem monotone_star {t : StarType} {r : Regex α} (rm : r.Monotone)
    : [/⟨r⟩*‹t›/].Monotone := by
  intro w s cap term
  rcases le_or_gt s w.length with sle | sgt
  · induction s, sle using decreasingStrongRec generalizing cap with | ind s sle ind =>
      simp only [matchPartial_star]
      cases t
      case greedy | lazy =>
        simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
          matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
          List.append_assoc, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
          List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, List.not_mem_nil,
          or_false, Prod.forall, Prod.mk.injEq]
        intro s' cap' or
        try rw [or_comm (a := _ ∧ cap' = _), or_assoc] at or
        rcases or with mem | ⟨s', cap', mem, mem'⟩ | mem
        · exact rm _ _ _ _ _ mem.1
        · have bound := endInBounds _ _ sle _ _ _ mem.1
          exact .trans (rm _ _ _ _ _ mem.1) (ind _ bound mem.2 _ _ _ mem')
        · simp [mem]
  · intro mat mem
    have bound := matchPartial_outOfBounds_eq (le_of_lt sgt) mem
    simp [bound]

theorem monotone : r.Monotone := by
  --by_cases! h : s ≤ w.length (by_cases unfolds Monotone and `intro`s variables :( )
  induction r with
  | bot => simp [Monotone, matchPartial_bot]
  | empty => simp [Monotone, matchPartial_empty]
  | unit _ => simp [Monotone, matchPartial_unit]
  | concat q r qind rind =>
    simp only [Monotone, matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
      ↓existsAndEq, true_and, forall_exists_index, Prod.forall]
    intro w s cap term s'' cap'' s' cap' qmem rmem
    specialize qind _ _ _ _ _ qmem
    specialize rind _ _ _ _ _ rmem
    simp only at qind rind
    exact .trans qind rind
  | or q r qind rind =>
    simp only [Monotone, matchPartial_or, List.mem_append, Prod.forall]
    intro w s cap term s' cap' mem
    exact Or.casesOn mem (fun mem ↦ qind _ _ _ _ _ mem) (fun mem ↦ rind _ _ _ _ _ mem)
  | filterEmpty e q qind =>
    simp only [Monotone, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
      Bool.decide_eq_true, List.mem_filter, beq_iff_eq, and_imp, Prod.forall]
    exact fun _ _ _ _ _ _ mem _ ↦ qind _ _ _ _ _ mem
  | star t q qind => exact monotone_star qind
  | start => simp [Monotone, matchPartial_start]
  | end' => simp [Monotone, matchPartial_end']
  | capture n q qind =>
    simp only [Monotone, matchPartial_capture, List.mem_map, Prod.eq_iff_fst_eq_snd_eq, Prod.exists,
      ↓existsAndEq, true_and, forall_exists_index, and_imp, Prod.forall, forall_apply_eq_imp_iff₂]
    exact fun _ _ _ _ _ _ mem ↦ qind _ _ _ _ _ mem
  | backref _ _ =>
    simp only [Monotone, matchPartial_backref, List.extract_eq_drop_take, List.length_take,
      List.length_drop, add_tsub_cancel_left, Prod.forall]
    intro w s cap term
    split <;> split <;> simp

end Regex
