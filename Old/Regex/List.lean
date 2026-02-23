import Mathlib.Tactic

set_option linter.unnecessarySimpa false

namespace List

variable {α : Type*}

section MinMax
variable [LinearOrder α] {top : α}

theorem min?_append_singleton (xs : List α) (x : α)
    : (xs ++ [x]).min? = some (xs.min?.elim x (min x)) := by
  induction xs with
  | nil => simp
  | cons x' xs xind =>
    simp only [cons_append, min?_cons, Option.elim, xind, Option.some.injEq]
    split <;> split <;> (
      expose_names; simp only [heq, Option.some.injEq, reduceCtorEq] at heq_1)
    · rw [heq_1, min_left_comm]
    · rw [min_comm]

theorem min?_get_le_of_mem' {l : List α} {a : α} (h : a ∈ l) :
    l.min?.get (isSome_min?_of_mem h) ≤ a := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [min?_cons, Option.get_some] at ih ⊢
    rcases mem_cons.1 h with (rfl|h)
    · cases t.min? with
      | none => simp
      | some b => simpa using Nat.min_le_left _ _
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (isSome_min?_of_mem h)
      simp only [hq, Option.elim_some] at ih ⊢
      exact le_trans (min_le_right _ _) (ih h)

theorem min?_getD_le_of_mem' {l : List α} {a k : α} (h : a ∈ l) : l.min?.getD k ≤ a :=
  Option.get_eq_getD _ ▸ min?_get_le_of_mem' h

theorem min?_getD_cons (a : α) (as : List α) (htop : ∀ a : α, a ≤ top)
    : (a :: as).min?.getD top = min a (as.min?.getD top) := by
  induction as with
  | nil => simp [htop a]
  | cons a as aind => simp

theorem min?_getD_append_singleton {a : α} (as : List α) (htop : ∀ a : α, a ≤ top)
    : (as ++ [a]).min?.getD top = min a (as.min?.getD top) := by
  induction as with
  | nil => simp [htop a]
  | cons a' as aind =>
    simp only [cons_append, min?_cons, min?_append_singleton,
      Option.elim_some, Option.getD_some]
    simp only [Option.elim]
    split <;> split <;> (
      expose_names; simp only [heq, Option.some.injEq, reduceCtorEq] at heq_1)
    · rw [heq_1, min_left_comm]
    · rw [min_comm]

--theorem min?_getD_append {xs : List α} {ys : List α} {k : α}
--    (exx : ys = [] → ∃ x ∈ xs, x ≤ k) (exy : xs = [] → ∃ y ∈ ys, y ≤ k)
--    : (xs ++ ys).min?.getD k = min (xs.min?.getD k) (ys.min?.getD k) := by
--  induction

theorem min?_getD_append_cons (xs : List α) {a : α} (ys : List α)
    (htop : ∀ a : α, a ≤ top)
    : (xs ++ a :: ys).min?.getD top = min a ((xs ++ ys).min?.getD top) := by
  induction xs with
  | nil => induction ys with
    | nil => simp [htop a]
    | cons => simp
  | cons x xs xind =>
    rw [cons_append, cons_append, min?_getD_cons, min?_getD_cons, xind,
      min_left_comm]
    · exact htop
    · exact htop

theorem min?_getD_append (xs ys : List α) (htop : ∀ a : α, a ≤ top)
    : (xs ++ ys).min?.getD top = min (xs.min?.getD top) (ys.min?.getD top) := by
  induction ys with
  | nil => simp [htop]
  | cons y ys yind => rw [min?_getD_append_cons _ _ htop, yind, min?_getD_cons _ _ htop,
    min_left_comm]

theorem min?_getD_append_comm (xs ys : List α) (htop : ∀ a : α, a ≤ top)
    : (xs ++ ys).min?.getD top = (ys ++ xs).min?.getD top := by
  rw [min?_getD_append _ _ htop, min?_getD_append _ _ htop, min_comm]

/-! ### max? -/

theorem le_max?_get_of_mem' {l : List α} {a : α} (h : a ∈ l) :
    a ≤ l.max?.get (isSome_max?_of_mem h) := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [max?_cons, Option.get_some] at ih ⊢
    rcases mem_cons.1 h with (rfl|h)
    · cases t.max? with
      | none => simp
      | some b => simpa using Nat.le_max_left _ _
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (isSome_max?_of_mem h)
      simp only [hq, Option.elim_some] at ih ⊢
      exact le_trans (ih h) (le_max_right _ _)

theorem le_max?_getD_of_mem' {l : List α} {a k : α} (h : a ∈ l) :
    a ≤ l.max?.getD k :=
  Option.get_eq_getD _ ▸ le_max?_get_of_mem' h

end MinMax

/-- If you somehow manage to get an element from `nil`, you goofed.
Defined because occasionally for some reason contradiction fails -/
theorem getElem_nil {a : α} {i : ℕ} {bound : i < [].length} : [][i] = a ↔ False := by
  contradiction

theorem lt_min_iff [LinearOrder α] [Std.LawfulOrderMin α]
    {l : List α} (hl : l ≠ []) : ∀ {x}, x < l.min hl ↔ ∀ b, b ∈ l → x < b := by
  intro x
  constructor
  · intro lt a al
    have min := List.min_le_of_mem al
    exact Trans.trans lt min
  · intro lt
    exact lt (l.min hl) (List.min_mem hl)

end List
