import Mathlib.Tactic

/-- A convenient structure to encode a dependent conjuncton of propositions.
`DAnd a b` represents `(x : a) ∧ b x`, aka `a ∧ ∀ x : a, b x` -/
structure DAnd (a : Prop) (b : a → Prop) : Prop where
  /-- `DAnd.intro : a → b → (x : a) ∧ b x` is the constructor for the DAnd operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : (x : a) ∧ b x` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : (x : a) ∧ b x` then
  `h.right`, also notated as `h.2`, is a dependent proof of `b`. -/
  right : b left

@[inherit_doc DAnd]
syntax:35 "(" ident " : " term:min ")" " ∧ " term:35 : term

macro_rules
  | `(( $x:ident : $a:term ) ∧ $b:term) => `(DAnd $a fun $x : $a ↦ $b)

section Unexpand
open Lean PrettyPrinter

@[app_unexpander DAnd]
def unexpDAnd : Unexpander
  | `($_ $a:term fun $x:ident : $_:term ↦ $b) => `(($x : $a) ∧ $b)
  | `($_ $a:term fun $x:ident ↦ $b) => `(($x : $a) ∧ $b)
  | _ => throw ()

end Unexpand

section Theorems
set_option linter.unusedVariables false

variable {a : Prop} {b : a → Prop}

@[simp] theorem dand_eq_and (p q : Prop) : ((x : p) ∧ q) = (p ∧ q) :=
  propext ⟨fun x ↦ ⟨x.1, x.2⟩, fun x ↦ ⟨x.1, x.2⟩⟩
@[simp] theorem dand_true (p : Prop) : ((x : p) ∧ True) = p := propext ⟨(·.1), (⟨·, trivial⟩)⟩
@[simp] theorem true_dand (p : Prop) : ((x : True) ∧ p) = p := propext ⟨(·.2), (⟨trivial, ·⟩)⟩
@[simp] theorem dand_false (p : Prop) : ((x : p) ∧ False) = False := eq_false (·.2)
@[simp] theorem false_dand (p : Prop) : ((x : False) ∧ p) = False := eq_false (·.1)
@[simp] theorem dand_self (p : Prop) : ((x : p) ∧ p) = p := propext ⟨(·.left), fun h => ⟨h, h⟩⟩
@[simp] theorem dand_not_self : ¬((x : a) ∧ ¬a) | ⟨ha, hn⟩ => absurd ha hn
@[simp] theorem not_dand_self : ¬((x : ¬a) ∧ a) := by simp
@[simp] theorem dand_imp : ((x : a) ∧ b x → c) ↔ ((x : a) → b x → c) :=
  ⟨fun h ha hb => h ⟨ha, hb⟩, fun h ⟨ha, hb⟩ => h ha hb⟩
@[simp] theorem not_dand : ¬((x : a) ∧ b x) ↔ ((x : a) → ¬b x) := dand_imp

/-- For converting between `DAnd` and `And` in the general case.
Notice that `a` gets mentioned twice in the `And`. -/
theorem dand_iff_and_forall : ((x : a) ∧ b x) ↔ a ∧ ∀ x, b x :=
  ⟨fun d ↦ ⟨d.1, fun _ ↦ d.2⟩, fun d ↦ ⟨d.1, d.2 d.1⟩⟩

end Theorems
