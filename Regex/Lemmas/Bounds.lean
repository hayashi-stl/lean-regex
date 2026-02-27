import Regex.Basic

/-! Lemmas about the bounds of matches. We also prove a convenient conditional
version of `terminates_star` -/

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : ℕ} {cap : Captures}

/-- If a start index that is `w.length` or out of bounds is supplied,
there are no positive-length matches. -/
theorem matchPartial_outOfBounds_eq {term : r.Terminates w s cap}
    (hs : w.length ≤ s) {mat} (mem : mat ∈ r.matchPartial w s cap term)
    : s = mat.1 := by
  induction r generalizing s cap mat with
  | bot => simp [matchPartial_bot] at mem
  | empty => simp [matchPartial_empty] at mem; simp [mem]
  | unit _ =>
    simp only [matchPartial_unit, List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rw [List.getElem?_eq_some_iff] at mem
    rcases mem with ⟨⟨lt, _⟩, _⟩
    exact (not_lt.mpr hs lt).elim
  | concat q r qind rind =>
    simp only [matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
      true_and] at mem
    rcases mem with ⟨s', cap', qmem, rmem⟩
    specialize qind hs qmem
    simp only at qind
    specialize rind (qind ▸ hs) rmem
    rw [← rind, ← qind]
  | or q r qind rind =>
    simp only [matchPartial_or, List.mem_append] at mem
    exact Or.casesOn mem (fun mem ↦ qind hs mem) (fun mem ↦ rind hs mem)
  | filterEmpty _ r rind =>
    simp only [matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
      Bool.decide_eq_true, List.mem_filter, beq_iff_eq] at mem
    exact rind hs mem.1
  | star t r rind =>
    simp only [matchPartial_star] at mem
    cases t
    case greedy | lazy =>
      simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
        matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
        List.append_assoc, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
        List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      try rw [or_comm (a := mat = _), or_assoc] at mem
      rcases mem with mem | ⟨s', cap', mem', _⟩ | eq
      · exact rind hs mem.1
      · specialize rind hs mem'.1; simp only at rind; exact
          (not_lt_iff_eq_or_lt.mpr (Or.inl rind) mem'.2).elim
      · simp [eq]
  | start => simp [matchPartial_start] at mem; simp [mem]
  | end' => simp [matchPartial_end'] at mem; simp [mem]
  | capture _ r rind =>
    simp only [matchPartial_capture, List.mem_map, Prod.exists] at mem
    rcases mem with ⟨s', cap', mem, up⟩
    specialize rind hs mem
    rw [Prod.eq_iff_fst_eq_snd_eq] at up
    simp at up
    simp [up, rind]
  | backref d _ =>
    simp only [matchPartial_backref, List.extract_eq_drop_take, List.length_take, List.length_drop,
      add_tsub_cancel_left] at mem
    split at mem
    · split at mem <;> (simp at mem; try simp [mem])
    · split at mem <;> (expose_names; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem)
      simp only [mem, Nat.left_eq_add, Nat.min_eq_zero_iff]
      simp only [List.drop_eq_nil_iff.mpr hs, List.take_nil, List.nil_eq, List.take_eq_nil_iff,
        List.drop_eq_nil_iff] at h
      rwa [← Nat.sub_eq_zero_iff_le] at h

/-- The property that matches with this regex always end in bounds
(i.e. at a position ≤ `w.length`) -/
def EndInBounds (r : Regex α) :=
  ∀ w s, s ≤ w.length → ∀ cap (term : r.Terminates w s cap) mat,
    mat ∈ r.matchPartial w s cap term → mat.1 ≤ w.length

/-- Stars end in bounds. Must be proved separately due to star recursion. -/
theorem endInBounds_star {t : StarType} (hr : r.EndInBounds)
    : [/⟨r⟩*‹t›/].EndInBounds := by
  intro w s sle cap term mat mem
  induction s, sle using decreasingStrongRec generalizing r cap mat with | ind s sle ind =>
  simp only [matchPartial_star] at mem
  cases t
  case greedy | lazy =>
    simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, iff_true,
      matchPartial_concat, Bool.false_eq_true, iff_false, not_le, matchPartial_empty,
      List.append_assoc, List.mem_append, List.mem_filter, decide_eq_true_eq, List.mem_flatten,
      List.mem_pmap, Prod.exists, ↓existsAndEq, true_and, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    try rw [or_comm (a := mat = _), or_assoc] at mem
    rcases mem with mem | ⟨s', cap', mem, stmem⟩ | eq
    · exact (.trans mem.2 sle)
    · exact ind s' (hr _ _ sle _ _ _ mem.1) mem.2 hr _ _ _ stmem
    · simp [eq, sle]

/-- If a start index that is at most `w.length` is supplied (i.e. is in bounds),
then all matches end in bounds. -/
theorem endInBounds : r.EndInBounds := by
  intro w s sle cap term mat mem
  induction r generalizing w s cap mat with
  | bot => simp [matchPartial_bot] at mem
  | empty => simp [matchPartial_empty, Prod.eq_iff_fst_eq_snd_eq] at mem; simp [mem, sle]
  | unit _ =>
    simp only [matchPartial_unit, List.getElem?_eq_some_iff, List.mem_ite_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    rcases mem with ⟨⟨lt, _⟩, mateq⟩
    simp [mateq, lt]
  | concat q r qind rind =>
    simp only [matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
      true_and] at mem
    rcases mem with ⟨s', cap', qmem, rmem⟩
    specialize qind _ _ sle _ _ _ qmem
    simp only at qind
    exact rind _ _ qind _ _ _ rmem
  | or q r qind rind =>
    simp only [matchPartial_or, List.mem_append] at mem
    exact Or.casesOn mem (fun mem ↦ qind _ _ sle _ _ _ mem) (fun mem ↦ rind _ _ sle _ _ _ mem)
  | filterEmpty _ r rind =>
    simp only [matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
      Bool.decide_eq_true, List.mem_filter, beq_iff_eq] at mem
    exact rind _ _ sle _ _ _ mem.1
  | star _ r rind =>
    exact endInBounds_star rind _ _ sle _ _ _ mem
  | start => simp [matchPartial_start] at mem; simp [mem]
  | end' => simp [matchPartial_end'] at mem; simp [mem]
  | capture _ r rind =>
    simp only [matchPartial_capture, List.mem_map, Prod.eq_iff_fst_eq_snd_eq, Prod.exists,
      ↓existsAndEq, true_and] at mem
    rcases mem with ⟨cap', mem, _⟩
    have le := rind _ _ sle _ _ _ mem
    exact le
  | backref d _ =>
    simp only [matchPartial_backref, List.extract_eq_drop_take, List.length_take, List.length_drop,
      add_tsub_cancel_left] at mem
    split at mem
    · split at mem <;> (simp at mem; try simp [mem, sle])
    · split at mem <;> (expose_names; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem)
      apply_fun List.length at h
      simp only [List.length_take, List.length_drop, Nat.min_assoc] at h
      simp only [mem, ← h]
      rw (occs := [3]) [← Nat.add_sub_cancel' sle]
      refine Nat.add_le_add_left ?_ s
      rw [min_comm, min_right_comm]
      exact min_le_right _ _

/-- `star t r` terminates if (but not only if)
`r` terminates for every capture and for every position starting from here -/
theorem terminates_star_of_forall {t : StarType}
    : (∀ s' ≥ s, ∀ cap', r.Terminates w s' cap') →
      [/⟨r⟩*‹t›/].Terminates w s cap := by
  intro term
  induction h : w.length - s using Nat.strongRec generalizing s cap with
  | ind n ind =>
    rw [terminates_star]
    refine ⟨term s (le_refl _) cap, fun mat mem lt ↦ ?_⟩
    simp only [← h] at ind
    by_cases! h : s < w.length
    · exact ind (w.length - mat.1) (Nat.sub_lt_sub_left h lt)
        (fun s' ge ↦ term s' (le_of_lt (Trans.trans lt ge))) rfl
    · have eq := matchPartial_outOfBounds_eq h mem
      exact (ne_of_lt lt eq).elim

/-- The star type is interchangeable in a `Terminates` assertion -/
theorem terminates_star_greedy_iff_lazy
    : [/⟨r⟩*/].Terminates w s cap ↔ [/⟨r⟩*?/].Terminates w s cap := by
  by_cases! sle : s ≤ w.length
  focus induction s, sle using decreasingStrongRec generalizing cap
  all_goals (
    simp only [terminates_star']
    rw [terminates_or_comm]
    simp only [terminates_or, terminates_filterEmpty, terminates_concat,
      matchPartial_filterEmpty, terminates_empty, true_and]
    rw [iff_iff_eq]; congr; ext term
    simp only [ge_iff_le, Bool.false_eq_true, eq_iff_iff, iff_false, not_le, List.mem_filter,
      decide_eq_true_eq, and_imp, Prod.forall])
  · rename_i s sle ind
    constructor <;> (
      intro left s' cap' mem lt
      have bound := endInBounds _ _ sle _ _ _ mem
      first | rw [ind _ bound lt] | rw [← ind _ bound lt]
      exact left _ _ mem lt)
  · constructor <;> (
      intro left s' cap' mem lt
      have bound := matchPartial_outOfBounds_eq (le_of_lt sle) mem
      linarith)

-- Some corollaries

theorem terminates_star_iff_greedy {t : StarType}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ [/⟨r⟩*/].Terminates w s cap := by
  cases t <;> simp [terminates_star_greedy_iff_lazy]

theorem terminates_star_iff_lazy {t : StarType}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ [/⟨r⟩*?/].Terminates w s cap := by
  cases t <;> simp [terminates_star_greedy_iff_lazy]

/-- The set of partial matches in the greedy and lazy versions of the same star
are the same. -/
theorem mem_matchPartial_star_greedy_iff_lazy {term : [/⟨r⟩*/].Terminates w s cap} {mat}
    : mat ∈ [/⟨r⟩*/].matchPartial w s cap term ↔
      mat ∈ [/⟨r⟩*?/].matchPartial w s cap (terminates_star_greedy_iff_lazy.mp term) := by
  by_cases! sle : s ≤ w.length
  focus induction s, sle using decreasingStrongRec generalizing cap
  all_goals (
    simp only [matchPartial_star]
    rw [mem_matchPartial_or_comm]
    simp only [matchPartial_or, matchPartial_empty, matchPartial_filterEmpty, ge_iff_le, eq_iff_iff,
      iff_true, matchPartial_concat, Bool.false_eq_true, iff_false, not_le, List.cons_append,
      List.nil_append, List.mem_cons, List.mem_append, List.mem_filter, decide_eq_true_eq,
      List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq, true_and]
    rw [iff_iff_eq]; congr; ext s'
  )
  · rename_i s sle ind
    constructor <;> (
      rintro ⟨cap', mem, mem'⟩
      have bound := endInBounds _ _ sle _ _ _ mem.1
      first | rw [ind _ bound mem.2] at mem' | rw [← ind _ bound mem.2] at mem'
      exact ⟨_, mem, mem'⟩)
    generalize_proofs term' at mem'
    exact terminates_star_greedy_iff_lazy.mpr term'
  · constructor <;> (
      rintro ⟨cap', mem, mem'⟩
      have bound := matchPartial_outOfBounds_eq (le_of_lt sle) mem.1
      linarith)

/-- The set of partial matches in the greedy and lazy versions of the same star
are the same. (lazy to greedy version, because a terminator is required) -/
theorem mem_matchPartial_star_lazy_iff_greedy {term : [/⟨r⟩*?/].Terminates w s cap} {mat}
    : mat ∈ [/⟨r⟩*?/].matchPartial w s cap term ↔
      mat ∈ [/⟨r⟩*/].matchPartial w s cap (terminates_star_greedy_iff_lazy.mpr term) := by
  rw [mem_matchPartial_star_greedy_iff_lazy]

-- Some corollaries

theorem mem_matchPartial_star_iff_greedy {t : StarType}
    {term : [/⟨r⟩*‹t›/].Terminates w s cap} {mat}
    : mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term ↔
      mat ∈ [/⟨r⟩*/].matchPartial w s cap (terminates_star_iff_greedy.mp term) := by
  cases t <;> simp [mem_matchPartial_star_greedy_iff_lazy]

theorem mem_matchPartial_star_iff_lazy {t : StarType}
    {term : [/⟨r⟩*‹t›/].Terminates w s cap} {mat}
    : mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term ↔
      mat ∈ [/⟨r⟩*?/].matchPartial w s cap (terminates_star_iff_lazy.mp term) := by
  cases t <;> simp [mem_matchPartial_star_greedy_iff_lazy]

end Regex
