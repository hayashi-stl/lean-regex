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
def AlwaysTerminates (r : Regex α) := ∀ w s cap, r.Terminates w s cap

theorem alwaysTerminates_bot : [/⊥/].AlwaysTerminates (α := α) :=
  fun _ _ _ ↦ terminates_bot

theorem alwaysTerminates_empty : [//].AlwaysTerminates (α := α) :=
  fun _ _ _ ↦ terminates_empty

theorem alwaysTerminates_unit {c : α} : [/c/].AlwaysTerminates (α := α) :=
  fun _ _ _ ↦ terminates_unit

theorem alwaysTerminates_concat {q r : Regex α}
    (qt : q.AlwaysTerminates) (rt : r.AlwaysTerminates)
    : [/⟨q⟩ ⟨r⟩/].AlwaysTerminates (α := α) :=
  fun w s cap ↦ terminates_concat.mpr ⟨qt w s cap, fun mat _ ↦ rt w mat.1 mat.2⟩

theorem alwaysTerminates_or {q r : Regex α}
    (qt : q.AlwaysTerminates) (rt : r.AlwaysTerminates)
    : [/⟨q⟩ | ⟨r⟩/].AlwaysTerminates (α := α) :=
  fun w s cap ↦ terminates_or.mpr ⟨qt w s cap, rt w s cap⟩

theorem alwaysTerminates_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/].AlwaysTerminates ↔ [/⟨r⟩ | ⟨q⟩/].AlwaysTerminates := by
  simp only [AlwaysTerminates, terminates_or_comm (q := q)]

theorem alwaysTerminates_filterEmpty {e : Bool} {r : Regex α}
    (rt : r.AlwaysTerminates)
    : [/⟨r⟩ ‹e›ε/].AlwaysTerminates (α := α) :=
  fun w s cap ↦ terminates_filterEmpty.mpr (rt w s cap)

theorem alwaysTerminates_star {t : StarType} {r : Regex α}
    (rt : r.AlwaysTerminates)
    : [/⟨r⟩*‹t›/].AlwaysTerminates (α := α) :=
  fun w _ _ ↦ terminates_star_of_forall fun s' _ cap' ↦ rt w s' cap'

theorem alwaysTerminates_star_greedy_iff_lazy {r : Regex α}
    : [/⟨r⟩*/].AlwaysTerminates ↔ [/⟨r⟩*?/].AlwaysTerminates := by
  simp only [AlwaysTerminates, terminates_star_greedy_iff_lazy]

theorem alwaysTerminates_start : [/⊢/].AlwaysTerminates (α := α) :=
  fun _ _ _ ↦ terminates_start

theorem alwaysTerminates_end' : [/⊣/].AlwaysTerminates (α := α) :=
  fun _ _ _ ↦ terminates_end'

theorem alwaysTerminates_capture {n : ℕ} {r : Regex α}
    (rt : r.AlwaysTerminates)
    : [/(‹n› ⟨r⟩)/].AlwaysTerminates (α := α) :=
  fun w s cap ↦ terminates_capture.mpr (rt w s cap)

theorem alwaysTerminates_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].AlwaysTerminates (α := α) := fun _ _ _ ↦ terminates_backref

/-- A class of regexes that can be proven to always terminate -/
inductive classTerminates : Regex α → Prop where
  | bot : classTerminates bot
  | empty : classTerminates empty
  | unit c : classTerminates (unit c)
  | concat q r : classTerminates q → classTerminates r → classTerminates (concat q r)
  | or q r : classTerminates q → classTerminates r → classTerminates (or q r)
  | filterEmpty e r : classTerminates r → classTerminates (filterEmpty e r)
  | star t r : classTerminates r → classTerminates (star t r)
  | start : classTerminates start
  | end' : classTerminates end'
  | capture n r : classTerminates r → classTerminates (capture n r)
  | backref d n : classTerminates (backref d n)

/-- Rexeges constructed out of just ones in `classTerminates` always terminate -/
theorem alwaysTerminates_classTerminates {r : Regex α} (hr : r.classTerminates)
    : r.AlwaysTerminates := by
  dsimp [AlwaysTerminates]
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
