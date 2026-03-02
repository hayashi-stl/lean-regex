import Regex.Match

variable {α : Type*} [deq : DecidableEq α] {r : Regex α} {w : List α}

namespace Regex

/-- Reversible regexes -/
inductive CReversible : Regex α → Prop where
  | bot : CReversible bot
  | empty : CReversible empty
  | unit c : CReversible (unit c)
  | concat q r : CReversible q → CReversible r → CReversible (concat q r)
  | or q r : CReversible q → CReversible r → CReversible (or q r)
  | star t r : CReversible r → CReversible (star t r)
  | start : CReversible start
  | end' : CReversible end'
  | capture n r : CReversible r → CReversible (capture n r)

/-- Whether a language is truly regular or just a faker. This is
why it's good to separate `Regex` from `RegularExpression`. -/
def Regular (r : Regex α) (term : ∀ w, r.Terminates w 0 0)
  := ∃ r' : RegularExpression α, r.language term = r'.matches'

end Regex
