import Regex.Basic

/-! Lemmas about the bounds of matches. We also prove a convenient conditional
version of `star_terminates` -/

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : ℕ} {cap : Captures} {term : r.Terminates w s cap}

def decreasingStrongRec {n : ℕ} {motive : (m : ℕ) → m ≤ n → Sort u}
    (ind : ∀ m, (mn : m ≤ n) →
      (∀ k, (kn : k ≤ n) → (km : k > m) → motive k kn) →
      motive m mn)
    (m : ℕ) (mn : m ≤ n)
    : motive m mn :=
  ind m mn fun k kn _ ↦ decreasingStrongRec ind k kn

/-- The property that all matches that end in bounds. -/
def EndsInBounds (r : Regex α) (w : List α) (s : ℕ) (cap : Captures)
    (term : r.Terminates w s cap) :=
    ∀ {mat},
      mat ∈ r.matchPartial w s cap term → mat.1 ≤ w.length

--/-- If a start index that is at most `w.length` is supplied (i.e. is in bounds),
--then all matches end in bounds. -/
--theorem matchPartial_inBounds_le (hs : s ≤ w.length) : r.EndsInBounds w s cap term := by
--  revert term
--  induction s, hs using decreasingStrongRec generalizing cap with | ind s slt ind =>
--    intro term
--    induction r with
--    | bot => simp [matchPartial_bot] at mem
--    | empty => simp [matchPartial_empty, Prod.eq_iff_fst_eq_snd_eq] at ind mem; simp [mem, slt]
--    | unit _ =>
--      simp only [matchPartial_unit, List.getElem?_eq_some_iff, List.mem_ite_nil_right, List.mem_cons,
--        List.not_mem_nil, or_false] at mem
--      rcases mem with ⟨⟨lt, _⟩, mateq⟩
--      simp [mateq, lt]
--    | concat q r qind rind =>
--      simp [matchPartial_concat] at ind mem
--      rcases mem with ⟨s', cap', qmem, rmem⟩
--      specialize qind hs qmem
--      simp only at qind
--      exact rind qind rmem
--    | or q r qind rind =>
--      simp only [matchPartial_or, List.mem_append] at mem
--      exact Or.casesOn mem (fun mem ↦ qind hs mem) (fun mem ↦ rind hs mem)
--    | filterEmpty _ r rind =>
--      simp only [matchPartial_filterEmpty, ge_iff_le, eq_iff_iff, Bool.decide_iff_dist,
--        Bool.decide_eq_true, List.mem_filter, beq_iff_eq] at mem
--      exact rind hs mem.1
--    | star t r rind =>
--      simp only [matchPartial_star] at mem
--      cases t
--      case greedy | lazy =>
--        simp [matchPartial_or, matchPartial_concat, matchPartial_filterEmpty,
--          matchPartial_empty] at mem
--        try rw [or_comm (a := mat = _), or_assoc] at mem
--        rcases mem with mem | ⟨s', cap', mem', _⟩ | eq
--        · exact rind hs mem.1
--        · specialize rind hs mem'.1; simp only at rind; exact _
--        · simp [eq]

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

/-- `star t r` terminates if (but not only if)
`r` terminates for every capture and for every position starting from here -/
theorem star_terminates_of_forall {t : StarType}
    : (∀ s' ≥ s, ∀ cap', r.Terminates w s' cap') →
      [/⟨r⟩*‹t›/].Terminates w s cap := by
  intro term
  induction h : w.length - s using Nat.strongRec generalizing s cap with
  | ind n ind =>
    rw [star_terminates]
    refine ⟨term s (le_refl _) cap, fun mat mem lt ↦ ?_⟩
    simp only [← h] at ind
    by_cases! h : s < w.length
    · exact ind (w.length - mat.1) (Nat.sub_lt_sub_left h lt)
        (fun s' ge ↦ term s' (le_of_lt (Trans.trans lt ge))) rfl
    · have eq := matchPartial_outOfBounds_eq h mem
      exact (ne_of_lt lt eq).elim

end Regex
