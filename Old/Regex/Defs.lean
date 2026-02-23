import Mathlib.Tactic
import Regex.PosCaptures

inductive Regex.StarType where
  /-- Higher numbers of matches have higher priority -/
  | greedy : StarType
  /-- Lower numbers of matches have higher priority -/
  | lazy : StarType
  deriving Repr

namespace Regex.StarType

theorem greedy_iff_not_lazy (t : StarType) : t = greedy ↔ t ≠ lazy := by
  cases t <;> simp

theorem lazy_iff_not_greedy (t : StarType) : t = lazy ↔ t ≠ greedy := by
  cases t <;> simp

end Regex.StarType

inductive Regex.BackrefDefault where
  /-- Fail if the capture doesn't exist -/
  | bot : BackrefDefault
  /-- Match the empty sequence if the capture doesn't exist -/
  | empty : BackrefDefault
  deriving Repr

namespace Regex.BackrefDefault

theorem bot_iff_not_empty (t : BackrefDefault) : t = bot ↔ t ≠ empty := by
  cases t <;> simp

theorem empty_iff_not_bot (t : BackrefDefault) : t = empty ↔ t ≠ bot := by
  cases t <;> simp

end Regex.BackrefDefault

open Regex.StarType Regex.BackrefDefault

/-- A regex structure to capture all features supported by regexes -/
inductive Regex (α : Type u) : Type u where
  /-- Always fails -/
  | bot : Regex α
  /-- Matches the empty sequence -/
  | empty : Regex α
  /-- Matches exactly `c` -/
  | unit (c : α) : Regex α
  /-- Matches `q` concatenated with `r` -/
  | concat (q r : Regex α) : Regex α
  /-- Matches `q` or `r`. `q` takes priority.-/
  | or (q r : Regex α) : Regex α
  /-- Matches a sequence iff `r` matches it and the sequence is empty or not,
  depending on `emp` -/
  | filterEmpty (emp : Bool) (r : Regex α) : Regex α
  --/-- Transform a list of matches based on `f` -/
  --| transform (f : {w : List α} → (s : Regex.Pos w)) (r : Regex α) : Regex α
  /-- Matches `r` 0 or more times. Priority depends on the star type. -/
  | star (t : Regex.StarType) (r : Regex α) : Regex α
  /-- Matches the start of the sequence -/
  | start : Regex α
  /-- Matches the end of the sequence -/
  | end' : Regex α
  /-- Captures the sequence matched by `r` into `n` -/
  | capture (n : ℕ) (r : Regex α) : Regex α
  /-- Matches exactly the sequence stored in capture `n`. If that doesn't exist,
  matches `default`. -/
  | backref (d : Regex.BackrefDefault) (n : ℕ) : Regex α
  deriving Repr

namespace Regex

/-- A computable version of sizeOf for regexes. There was no reason for `sizeOf`
to be noncomputable. -/
def depth {α : Type*} (r : Regex α) : ℕ := match r with
  | bot => 0
  | empty => 0
  | unit _ => 0
  | concat q r => q.depth + r.depth + 1
  | or q r => q.depth + r.depth + 1
  | filterEmpty _ r => r.depth + 1
  | star _ r => r.depth + 1
  | start => 0
  | end' => 0
  | capture _ r => r.depth + 1
  | backref _ _ => 0

def list {α : Type*} (w : List α) : Regex α := match w with
  | [] => empty
  | a :: as => concat (unit a) (list as)

def string (w : String) := list w.toList

end Regex
