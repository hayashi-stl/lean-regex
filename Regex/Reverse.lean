import Regex.Match
import Regex.Lemmas.Equiv

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w} {mat : Pos w × Captures w}

/-- Reversible regexes -/
inductive CReversible : Regex α → Type u where
  | bot : CReversible bot
  | empty : CReversible empty
  | unit c : CReversible (unit c)
  | concat {q} {r} : CReversible q → CReversible r → CReversible (concat q r)
  | or {q} {r} : CReversible q → CReversible r → CReversible (or q r)
  | star t {r} : CReversible r → CReversible (star t r)
  | start : CReversible start
  | end' : CReversible end'
  | capture n {r} : CReversible r → CReversible (capture n r)

namespace CReversible

def cTerminates {r : Regex α} (hr : r.CReversible)
    : r.CTerminates := match hr with
  | bot => CTerminates.bot
  | empty => CTerminates.empty
  | unit _ => CTerminates.unit _
  | concat qt rt => CTerminates.concat qt.cTerminates rt.cTerminates
  | or qt rt => CTerminates.or qt.cTerminates rt.cTerminates
  | star t rt => CTerminates.star t rt.cTerminates
  | start => CTerminates.start
  | end' => CTerminates.end'
  | capture n rt => CTerminates.capture n rt.cTerminates

theorem allTerminates {r : Regex α} (hr : r.CReversible) :
  r.AllTerminates := hr.cTerminates.allTerminates

/-- Reverse a reversible regex. -/
def reverse {r : Regex α} (hr : CReversible r)
    : (r : Regex α) × r.CReversible := match hr with
  | bot => ⟨_, bot⟩
  | empty => ⟨_, empty⟩
  | unit c => ⟨_, unit c⟩
  | concat q r => ⟨_, concat r.reverse.2 q.reverse.2⟩
  | or q r => ⟨_, or q.reverse.2 r.reverse.2⟩
  | star t r => ⟨_, star t r.reverse.2⟩
  | start => ⟨_, start⟩
  | end' => ⟨_, end'⟩
  | capture n r => ⟨_, capture n r.reverse.2⟩

omit deq in
/-- Reversing is an involution -/
theorem reverse_reverse {r : Regex α} (hr : CReversible r)
    : hr.reverse.2.reverse.1 = r := by
  induction hr with
  | bot => simp [reverse]
  | empty => simp [reverse]
  | unit => simp [reverse]
  | concat q r qind rind => simp [reverse, qind, rind]
  | or q r qind rind => simp [reverse, qind, rind]
  | star t r rind => simp [reverse, rind]
  | start => simp [reverse]
  | end' => simp [reverse]
  | capture n r rind => simp [reverse, rind]

/-- Encoding the reversibility property -/
def Reversible' {r : Regex α} (hr : CReversible r) :=
  ∀ w s cap term mat, mat ∈ r.matchPartial w s cap term → ∃ cap',
    (s.reverse, cap') ∈ hr.reverse.1.matchPartial w.reverse
      mat.1.reverse mat.2.reverse (hr.reverse.2.allTerminates _ _ _)

/-- Encoding the reversibility property (iff version) -/
def Reversible {r : Regex α} (hr : CReversible r) :=
  ∀ w s cap term mat, mat ∈ r.matchPartial w s cap term ↔
    (s.reverse, cap.reverse) ∈ hr.reverse.1.matchPartial w.reverse
      mat.1.reverse mat.2.reverse (hr.reverse.2.allTerminates _ _ _)

theorem mem_matchPartial_reverse_bot : CReversible.bot.Reversible' (α := α) := by
  simp [Reversible', reverse, matchPartial_bot]

theorem mem_matchPartial_reverse_empty : CReversible.empty.Reversible' (α := α) := by
  simp [Reversible', reverse, matchPartial_empty]

theorem mem_matchPartial_reverse_unit {c : α} : (CReversible.unit c).Reversible' := by
  simp only [Reversible', matchPartial_unit, List.mem_dite_nil_right, List.mem_cons,
    List.not_mem_nil, or_false, reverse, Pos.val_reverse, Prod.mk.injEq, exists_and_right,
    forall_exists_index, forall_eq_apply_imp_iff, Pos.val_succOfIndex, and_true]
  refine fun w s cap term wsc ↦ ⟨?_, ?_⟩
  · rwa [List.getElem?_reverse, Nat.add_comm, Nat.sub_add_eq, Nat.sub_sub_self]
    all_goals have ⟨lt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
    · rw [Nat.le_sub_iff_add_le (by linarith)]
      exact Nat.add_one_le_of_lt lt
    · rw [Nat.sub_lt_iff_lt_add (Nat.add_one_le_of_lt lt)]
      linarith
  · simp only [← Fin.val_inj, Pos.val_reverse, Pos.val_succOfIndex]
    rw [Nat.sub_add_eq, Nat.sub_add_cancel]
    have ⟨lt, wsc⟩ := List.getElem?_eq_some_iff.mp wsc
    rw [Nat.le_sub_iff_add_le s.is_le]
    exact Nat.one_add_le_iff.mpr lt

theorem mem_matchPartial_reverse_concat {q r : Regex α} {hq : CReversible q}
    {hr : CReversible r} (qrev : hq.Reversible') (rrev : hr.Reversible')
    : (CReversible.concat hq hr).Reversible' := by
  simp only [Reversible', matchPartial_concat, List.mem_flatten, List.mem_pmap, Prod.exists,
    ↓existsAndEq, true_and, reverse, forall_exists_index, Prod.forall]
  intro w s cap term s'' cap'' s' cap' qmem rmem
  have memr := rrev w s' cap' ((terminates_concat.mp term).2 _ qmem) _ rmem
  have memq := qrev w s cap (terminates_concat.mp term).1 _ qmem
  exact ⟨_, _, memr, memq⟩

theorem mem_matchPartial_reverse_or {q r : Regex α} {hq : CReversible q}
    {hr : CReversible r} (qrev : hq.Reversible') (rrev : hr.Reversible')
    : (CReversible.or hq hr).Reversible' := by
  simp only [Reversible', matchPartial_or, List.mem_append, reverse, Prod.forall]
  rintro w s cap term s' cap' (qmem | rmem)
  · exact Or.inl (qrev w s cap (terminates_or.mp term).1 _ qmem)
  · exact Or.inr (rrev w s cap (terminates_or.mp term).2 _ rmem)

theorem mem_matchPartial_reverse_star {t : StarType} {r : Regex α}
    {hr : CReversible r} (rrev : hr.Reversible')
    : (CReversible.star t hr).Reversible' := by
  simp only [Reversible', reverse, (matchPartialEquiv_star_type (t := t) .greedy).2]
  intro w s
  induction s using Pos.strongRecEnd with | ind s ind =>
    conv in _ ∈ _ => rw [matchPartial_star]
    conv => pattern (occs := 2) _ ∈ _; rw [matchPartial_star]
    simp only [List.mem_append, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
      true_and, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Prod.forall]
    rintro cap term s'' cap'' (⟨s', cap', mem, mem'⟩ | eq)
    · split at mem' <;> rename_i hs
      · specialize ind _ hs _ ((CReversible.star t hr).allTerminates _ _ _) _ mem'
        have memr := rrev w s cap (hr.allTerminates _ _ _) _ mem
        refine Or.inl ⟨_, _, memr, ?_⟩

/-- Reversing actually works. -/
theorem mem_matchPartial_reverse {r : Regex α} (hr : CReversible r) {w : List α}
    {s : Pos w} {cap : Captures w} {mat}
    : mat ∈ r.matchPartial w s cap (hr.allTerminates _ _ _) ↔
      (s.reverse, cap.reverse) ∈ hr.reverse.1.matchPartial w.reverse
        mat.1.reverse mat.2.reverse (hr.reverse.2.allTerminates _ _ _) := by


end CReversible

end Regex
