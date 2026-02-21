import Mathlib.Tactic

-- `Except` needs a lot more theorems...

namespace Except

variable {«ε» α : Type*} {x : Except «ε» α}

@[simp] theorem ok_inj (a b : α) : Except.ok («ε» := «ε») a = Except.ok b ↔ a = b :=
  iff_eq_eq ▸ Except.ok.injEq a b

@[simp] theorem error_inj (a b : «ε»)
  : Except.error (α := α) a = Except.error b ↔ a = b :=
  iff_eq_eq ▸ Except.error.injEq a b

theorem ok_eq_pure : Except.ok («ε» := «ε») (α := α) = pure := rfl

@[simp] theorem ok_bind (a : α) (f : α → Except «ε» α) : ok a >>= f = f a := rfl

@[simp] theorem error_bind (e : «ε») (f : α → Except «ε» α) : error e >>= f = error e := by rfl

@[simp] theorem bind_ok (x : Except «ε» α) : x >>= ok = x := by
  simp [ok_eq_pure, bind_pure]

theorem eq_ok_or_eq_error (x : Except «ε» α)
    : (∃ a, x = ok a) ∨ (∃ e, x = error e) := by
  cases h : x with
  | ok a => exact Or.inl ⟨a, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

theorem eq_error_iff_forall_ne_ok {x : Except «ε» α}
    : (∀ a, x ≠ ok a) ↔ ∃ e, x = error e := by
  constructor
  · have := or_iff_not_imp_left.mp (eq_ok_or_eq_error x)
    push_neg at this
    exact this
  · intro ex a
    by_contra!
    simp [this] at ex

end Except
