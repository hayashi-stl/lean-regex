import Regex.Lemmas.Equiv

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w} {mat : Pos w × Captures w}

/-- A class of regular expressions that include anchors -/
inductive CRegularAnchor : Regex α → Type u where
  | bot : CRegularAnchor bot
  | empty : CRegularAnchor empty
  | unit c : CRegularAnchor (unit c)
  | concat {q} {r} : CRegularAnchor q → CRegularAnchor r → CRegularAnchor (concat q r)
  | or {q} {r} : CRegularAnchor q → CRegularAnchor r → CRegularAnchor (or q r)
  | star t {r} : CRegularAnchor r → CRegularAnchor (star t r)
  | start : CRegularAnchor start
  | end' : CRegularAnchor end'
  | capture n {r} : CRegularAnchor r → CRegularAnchor (capture n r)

namespace CRegularAnchor

set_option linter.unusedVariables false in
def regex {r : Regex α} (hr : r.CRegularAnchor) := r

omit deq in
@[simp] theorem regex_eq {r : Regex α} (hr : r.CRegularAnchor) : hr.regex = r := rfl

/-- Get a regex that's language-equivalent to this regex, but doesn't
have any start anchors, assuming that `start` equals `bot` -/
def simpStartToBot {r : Regex α} (hr : r.CRegularAnchor)
    : (r : Regex α) × r.CRegularAnchor :=
  match hr with
  | bot => ⟨_, bot⟩
  | empty => ⟨_, empty⟩
  | unit c => ⟨_, unit c⟩
  | concat q r => ⟨_, concat q.simpStartToBot.2 r.simpStartToBot.2⟩
  | or q r => ⟨_, or q.simpStartToBot.2 r.simpStartToBot.2⟩
  | star t r => ⟨_, star t r.simpStartToBot.2⟩
  | start => ⟨_, bot⟩ -- here!
  | end' => ⟨_, end'⟩
  | capture n r => ⟨_, capture n r.simpStartToBot.2⟩

def HasStart {r : Regex α} (hr : r.CRegularAnchor) := match hr with
  | bot => False
  | empty => False
  | unit _ => False
  | concat q r => q.HasStart ∨ r.HasStart
  | or q r => q.HasStart ∨ r.HasStart
  | star _ r => r.HasStart
  | start => True
  | end' => False
  | capture _ r => r.HasStart

/-- A termination measure of `simpStart` based on
how left-associative `concats` are. Used to break ties. -/
def simpStartSize {r_ : Regex α} (hr : r_.CRegularAnchor) : ℕ :=
  match hr with
  | concat (concat p _) _ => p.regex.depth + 1
  | _ => 0

omit deq in
theorem simpStartSize_concat_right_lt_left {p q r : Regex α}
    (hp : p.CRegularAnchor) (hq : q.CRegularAnchor) (hr : r.CRegularAnchor)
    : (concat hp (concat hq hr)).simpStartSize < (concat (concat hp hq) hr).simpStartSize := by
  induction hp
  case concat o p ho hp oind pind =>
    simp [simpStartSize, Regex.depth]
  all_goals simp [simpStartSize]

/-- Induction rule for `simpStart`, since its recursion is weird -/
def simpStartRec {motive : {r : Regex α} → r.CRegularAnchor → Sort*}
    (bot : motive bot)
    (empty : motive empty)
    (unit : (c : α) → motive (unit c))
    (bot_concat : {r : Regex α} → (hr : r.CRegularAnchor) → motive (concat .bot hr))
    (empty_concat : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (concat .empty hr))
    (unit_concat : (c : α) → {r : Regex α} → (hr : r.CRegularAnchor) →
      motive (concat (.unit c) hr))
    (concat_concat : {p q r : Regex α} → (hp : p.CRegularAnchor) →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive (concat hp (concat hq hr)) → motive (concat (concat hp hq) hr))
    (or_concat : {p q r : Regex α} → (hp : p.CRegularAnchor) →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive (concat hp hr) → motive (concat hq hr) → motive (concat (or hp hq) hr))
    (star_concat : (t : StarType) → {q r : Regex α} →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive hq → motive hr → motive (concat (star t hq) hr))
    (start_concat : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive (concat .start hr))
    (end'_concat : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive (concat .end' hr))
    (capture_concat : {n : ℕ} → {q r : Regex α} →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive (concat hq hr) → motive (concat (capture n hq) hr))
    (or : {q r : Regex α} → (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive hq → motive hr → motive (or hq hr))
    (star : (t : StarType) → {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (star t hr))
    (start : motive start)
    (end' : motive end')
    (capture : (n : ℕ) → {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (capture n hr))
    {r : Regex α} (hr : r.CRegularAnchor)
    : motive hr :=
  match hr with
  | .bot => bot
  | .empty => empty
  | .unit c => unit c
  | .concat .bot r => bot_concat r
  | .concat .empty r => empty_concat r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture r)
  | .concat (.unit c) r => unit_concat r


/-- Get a regex that's language-equivalent to this regex, but doesn't
have any start anchors. -/
def simpStart {r : Regex α} (hr : r.CRegularAnchor)
    : (r : Regex α) × r.CRegularAnchor :=
  match hr with
  | bot => ⟨_, bot⟩
  | empty => ⟨_, empty⟩
  | unit c => ⟨_, unit c⟩
  | concat bot r => ⟨_, bot⟩
  | concat empty r => ⟨_, r.simpStart.2⟩
  | concat (unit _) r => ⟨_, r.simpStartToBot.2⟩
  | concat (concat p q) r => (concat p (concat q r)).simpStart
  | concat (or p q) r => ⟨_, or (concat p r).simpStart.2 (concat q r).simpStart.2⟩
  | concat (star t q) r => ⟨_, or r.simpStart.2 (concat q.simpStart.2
      (concat (star t q.simpStartToBot.2) r.simpStartToBot.2))⟩
  | concat start r => ⟨_, r.simpStart.2⟩
  | concat end' r => ⟨_, r.simpStart.2⟩
  | concat (capture n q) r => (concat q r).simpStart
  | or q r => ⟨_, or q.simpStart.2 r.simpStart.2⟩
  | star t r => ⟨_, or empty (concat r.simpStart.2 (star t r.simpStartToBot.2))⟩
  | start => ⟨_, empty⟩
  | end' => ⟨_, end'⟩
  | capture n r => ⟨_, capture n r.simpStart.2⟩
termination_by (hr.regex.depth, hr.simpStartSize)
decreasing_by
  rotate_left 1
  · simp only [regex_eq, depth, simpStartSize, Prod.lex_def, Order.lt_add_one_iff,
      Order.add_one_le_iff, Nat.add_right_cancel_iff]
    right
    constructor
    · rw [Nat.add_right_comm]; simp [Nat.add_assoc]
    split
    · expose_names; simp at heq; simp [heq.1, depth]
    · exact Nat.zero_le _
  all_goals simp [Prod.lex_def, simpStartSize, depth] <;> try linarith

omit deq in
/-- `simpStartToBot` removes all start anchors -/
theorem simpStartToBot_noStart {r : Regex α} (hr : r.CRegularAnchor)
    : ¬hr.simpStartToBot.2.HasStart := by
  induction hr <;> simp [simpStartToBot, HasStart, *]

/-- `simpStartToBot` removes all start anchors -/
theorem simpStart_noStart {r : Regex α} (hr : r.CRegularAnchor)
    : ¬hr.simpStart.2.HasStart := by
  induction hr using simpStartRec
  --induction (hr.regex.depth, hr.simpStartSize)
  --induction hr <;> try rw [simpStart.eq_def]; simp [HasStart, *]
  --case concat q r qind rind =>
  --  cases q

end CRegularAnchor

end Regex
