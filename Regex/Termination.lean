import Regex.Basic

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

/-- A class of regexes that can be proven to terminate -/
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
theorem classTerminates_terminates (r : Regex α) (hr : r.classTerminates)
    : ∀ w s cap, r.Terminates w s cap := by
  induction hr with
  | bot => termination
  | empty => termination
  | unit c => termination
  | concat q r _ _ qt rt => simp [concat_terminates, qt, rt]
  | or q r _ _ qt rt => simp [or_terminates, qt, rt]
  | filterEmpty e r _ rt => simp [filterEmpty_terminates, rt]
  | star t r _ rt => intro r s cap; apply star_terminates_of_forall; simp [rt]
  | start => termination
  | end' => termination
  | capture n r _ rt => simp [capture_terminates, rt]
  | backref d n => termination

end Regex
