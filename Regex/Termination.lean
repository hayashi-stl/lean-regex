import Regex.Lemmas.Bounds

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

section Tactic

open Lean Parser Tactic

macro "termination" : tactic =>
  `(tactic| (repeat simp [
    terminates_bot, terminates_empty, terminates_unit, terminates_concat,
    terminates_or, terminates_filterEmpty, terminates_start, terminates_end',
    terminates_capture, terminates_backref, terminates_star_of_forall];
    ))

end Tactic

/-- A regex that always terminates, regardless of inputs to `matchPartial` -/
def AllTerminates (r : Regex α) := ∀ w s cap, r.Terminates w s cap

theorem allTerminates_bot : [/⊥/].AllTerminates (α := α) :=
  fun _ _ _ ↦ terminates_bot

theorem allTerminates_empty : [//].AllTerminates (α := α) :=
  fun _ _ _ ↦ terminates_empty

theorem allTerminates_unit {c : α} : [/c/].AllTerminates (α := α) :=
  fun _ _ _ ↦ terminates_unit

theorem allTerminates_concat {q r : Regex α}
    (qt : q.AllTerminates) (rt : r.AllTerminates)
    : [/⟨q⟩ ⟨r⟩/].AllTerminates (α := α) :=
  fun w s cap ↦ terminates_concat.mpr ⟨qt w s cap, fun mat _ ↦ rt w mat.1 mat.2⟩

theorem allTerminates_or {q r : Regex α}
    (qt : q.AllTerminates) (rt : r.AllTerminates)
    : [/⟨q⟩ | ⟨r⟩/].AllTerminates (α := α) :=
  fun w s cap ↦ terminates_or.mpr ⟨qt w s cap, rt w s cap⟩

theorem allTerminates_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/].AllTerminates ↔ [/⟨r⟩ | ⟨q⟩/].AllTerminates := by
  simp only [AllTerminates, terminates_or_comm (q := q)]

theorem allTerminates_filterEmpty {e : Bool} {r : Regex α}
    (rt : r.AllTerminates)
    : [/⟨r⟩ ‹e›ε/].AllTerminates (α := α) :=
  fun w s cap ↦ terminates_filterEmpty.mpr (rt w s cap)

theorem allTerminates_star {t : StarType} {r : Regex α}
    (rt : r.AllTerminates)
    : [/⟨r⟩*‹t›/].AllTerminates (α := α) :=
  fun w _ _ ↦ terminates_star_of_forall fun s' _ cap' ↦ rt w s' cap'

theorem allTerminates_star_greedy_iff_lazy {r : Regex α}
    : [/⟨r⟩*/].AllTerminates ↔ [/⟨r⟩*?/].AllTerminates := by
  simp only [AllTerminates, terminates_star_greedy_iff_lazy]

theorem allTerminates_start : [/⊢/].AllTerminates (α := α) :=
  fun _ _ _ ↦ terminates_start

theorem allTerminates_end' : [/⊣/].AllTerminates (α := α) :=
  fun _ _ _ ↦ terminates_end'

theorem allTerminates_capture {n : ℕ} {r : Regex α}
    (rt : r.AllTerminates)
    : [/(‹n› ⟨r⟩)/].AllTerminates (α := α) :=
  fun w s cap ↦ terminates_capture.mpr (rt w s cap)

theorem allTerminates_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].AllTerminates (α := α) := fun _ _ _ ↦ terminates_backref

/-- A class of regexes that can be proven to always terminate -/
inductive CTerminates : Regex α → Prop where
  | bot : CTerminates bot
  | empty : CTerminates empty
  | unit c : CTerminates (unit c)
  | concat q r : CTerminates q → CTerminates r → CTerminates (concat q r)
  | or q r : CTerminates q → CTerminates r → CTerminates (or q r)
  | filterEmpty e r : CTerminates r → CTerminates (filterEmpty e r)
  | star t r : CTerminates r → CTerminates (star t r)
  | start : CTerminates start
  | end' : CTerminates end'
  | capture n r : CTerminates r → CTerminates (capture n r)
  | backref d n : CTerminates (backref d n)

/-- Rexeges constructed out of just ones in `cTerminates` always terminate -/
theorem CTerminates.allTerminates {r : Regex α} (hr : r.CTerminates)
    : r.AllTerminates := by
  dsimp [AllTerminates]
  induction hr with
  | bot => termination
  | empty => termination
  | unit c => termination
  | concat q r _ _ qt rt => simp [terminates_concat, qt, rt]
  | or q r _ _ qt rt => simp [terminates_or, qt, rt]
  | filterEmpty e r _ rt => simp [terminates_filterEmpty, rt]
  | star t r _ rt => intro r s cap; apply terminates_star_of_forall; simp [rt]
  | start => termination
  | end' => termination
  | capture n r _ rt => simp [terminates_capture, rt]
  | backref d n => termination

end Regex
