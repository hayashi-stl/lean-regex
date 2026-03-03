import Regex.Termination

/-! Lemmas about `matchPartial` membership -/

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {q r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w} {mat : Pos w × Captures w}

theorem mem_matchPartial_bot : ¬mat ∈ [/⊥/].matchPartial w s cap terminates_bot := by
  simp [matchPartial_bot]

theorem mem_matchPartial_empty
    : mat ∈ [//].matchPartial w s cap terminates_empty ↔ mat = (s, cap) := by
  simp [matchPartial_empty]

theorem mem_matchPartial_unit {c : α}
    : mat ∈ [/c/].matchPartial w s cap terminates_unit ↔
      ∃ wsc : w[s.val]? = c, mat = (s.succOfIndex wsc, cap) := by
  simp [matchPartial_unit]

theorem mem_matchPartial_concat {q r : Regex α} (term)
    : mat ∈ [/⟨q⟩ ⟨r⟩/].matchPartial w s cap term ↔
      ∃ mid, ∃ mem : mid ∈ q.matchPartial w s cap (terminates_concat.mp term).1,
        mat ∈ r.matchPartial w mid.1 mid.2 ((terminates_concat.mp term).2 _ mem) := by
  simp [matchPartial_concat]

theorem mem_matchPartial_or {q r : Regex α} (term)
    : mat ∈ [/⟨q⟩ | ⟨r⟩/].matchPartial w s cap term ↔
        mat ∈ q.matchPartial w s cap (terminates_or.mp term).1 ∨
        mat ∈ r.matchPartial w s cap (terminates_or.mp term).2 := by
  simp [matchPartial_or]

theorem mem_matchPartial_star (term)
    : mat ∈ [/⟨r⟩*/].matchPartial w s cap term ↔
      mat = (s, cap) ∨
      ∃ mid, ∃ mem : mid ∈ r.matchPartial w s cap (terminates_star.mp term).1,
        if h : s < mid.1
          then mat ∈ [/⟨r⟩*/].matchPartial w mid.1 mid.2
            ((terminates_star.mp term).2 _ mem h)
          else mat = mid := by
  rw [matchPartial_star]
  simp only [Prod.exists]
  simp only [List.mem_append, List.mem_flatten, List.mem_pmap, Prod.exists, ↓existsAndEq,
    true_and, List.mem_cons, List.not_mem_nil, or_false]
  try rw [or_comm (b := mat = _)]
  rw [iff_eq_eq]; congr; ext x;
  rw [iff_eq_eq]; congr; ext x';
  rw [iff_eq_eq]; congr; ext x'';
  rw [iff_eq_eq]
  split <;> simp

theorem mem_matchPartial_start
    : mat ∈ [/⊢/].matchPartial w s cap terminates_start ↔
      s = 0 ∧ mat = (s, cap) := by
  simp [matchPartial_start]

theorem mem_matchPartial_end'
    : mat ∈ [/⊣/].matchPartial w s cap terminates_end' ↔
      s = w.length ∧ mat = (s, cap) := by
  simp [matchPartial_end']

theorem mem_matchPartial_capture {n : ℕ} {term}
    : mat ∈ [/(n ← ⟨r⟩)/].matchPartial w s cap term ↔
      ∃ mid ∈ r.matchPartial w s cap (terminates_capture.mp term),
      mat = (mid.1, mid.2.update n [(s, mid.1)]) := by
  simp [matchPartial_capture, eq_comm (a := mat)]

theorem mem_matchPartial_list {l : List α}
    : mat ∈ (list l).matchPartial w s cap terminates_list ↔
      ∃ wsl : w.extract s (s + l.length) = l, mat = (s.addOfIndex wsl rfl, cap) := by
  simp [matchPartial_list]

theorem mem_matchPartial_backref {d : BackrefDefault} {n : ℕ}
    : mat ∈ [/\‹d›n/].matchPartial w s cap terminates_backref ↔
      match (cap n).head? with
      | none => d = .empty ∧ mat = (s, cap)
      | some (cs, ct) => ∃ h : w.extract s (s + (ct - cs)) = w.extract cs ct,
          mat = (s.addOfIndex h (List.length_extract_pos _ _), cap) := by
  simp only [matchPartial_backref]
  split <;> split <;> split <;> expose_names
  all_goals try { simp [*] at * }
  · simp only [heq, Option.some.injEq, Prod.mk.injEq] at heq_1; simp [← heq_1, h]
  · simp only [heq, Option.some.injEq, Prod.mk.injEq] at heq_1
    simp only [← heq_1, h]
    simp

end Regex
