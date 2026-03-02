import Regex.Lemmas.Equiv

/-! Here we prove monotonicity of regex matches. A regex match does not
end before it starts. -/

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w} {term : r.Terminates w s cap}

/-- Regexes where matches don't end before they start (all the regexes) -/
def Monotone (r : Regex α) :=
    ∀ w s cap (term : r.Terminates w s cap)
    mat, mat ∈ r.matchPartial w s cap term → s ≤ mat.1

theorem monotone_star {t : StarType} {r : Regex α} (rm : r.Monotone)
    : [/⟨r⟩*‹t›/].Monotone := by
  rw [Monotone]
  conv in Terminates _ _ _ _ => rw [terminatesEquiv_star_type .greedy]
  conv in _ ∈ _ => rw [(matchPartialEquiv_star_type .greedy).2]
  intro w s cap term
  induction s using Pos.strongRecEnd generalizing cap with | ind s ind =>
    conv in _ ∈ _ => rw [matchPartial_star]
    simp only [List.mem_append, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
      true_and, List.mem_cons, List.not_mem_nil, or_false, Prod.forall, Prod.mk.injEq]
    intro s'' cap'' or
    rcases or with ⟨s', cap', mem, mem'⟩ | mem
    · rcases lt_or_eq_of_le (rm _ _ _ _ _ mem) with lt | eq
      · simp only [lt, ↓reduceDIte] at mem'
        exact le_of_lt (trans lt (ind _ lt _ ((terminates_star.mp term).2 _ mem lt) _ mem'))
      · simp [eq] at mem'; simp [eq, mem']
    · simp [mem]

theorem monotone : r.Monotone := by
  --by_cases! h : s ≤ w.length (by_cases unfolds Monotone and `intro`s variables :( )
  induction r with
  | bot => simp [Monotone, matchPartial_bot]
  | empty => simp [Monotone, matchPartial_empty]
  | unit _ => simp [Monotone, matchPartial_unit, ← Fin.val_fin_le]
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
  | star t q qind => exact monotone_star qind
  | start => simp [Monotone, matchPartial_start]
  | end' => simp [Monotone, matchPartial_end']
  | capture n q qind =>
    simp only [Monotone, matchPartial_capture, List.mem_map, Prod.eq_iff_fst_eq_snd_eq, Prod.exists,
      ↓existsAndEq, true_and, forall_exists_index, and_imp, Prod.forall, forall_apply_eq_imp_iff₂]
    exact fun _ _ _ _ _ _ mem ↦ qind _ _ _ _ _ mem
  | backref _ _ =>
    simp only [Monotone, matchPartial_backref, List.extract_eq_drop_take,
      add_tsub_cancel_left, Prod.forall]
    intro w s cap term
    split <;> split <;> simp [← Fin.val_fin_le]

end Regex
