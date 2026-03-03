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
  | star {r} : CRegularAnchor r → CRegularAnchor (star r)
  | start : CRegularAnchor start
  | end' : CRegularAnchor end'
  | capture n {r} : CRegularAnchor r → CRegularAnchor (capture n r)

namespace CRegularAnchor

set_option linter.unusedVariables false in
def regex {r : Regex α} (hr : r.CRegularAnchor) := r

omit deq in
@[simp] theorem regex_eq {r : Regex α} (hr : r.CRegularAnchor) : hr.regex = r := rfl

def cTerminates {r : Regex α} (hr : r.CRegularAnchor)
    : r.CTerminates := match hr with
  | bot => CTerminates.bot
  | empty => CTerminates.empty
  | unit _ => CTerminates.unit _
  | concat qt rt => CTerminates.concat qt.cTerminates rt.cTerminates
  | or qt rt => CTerminates.or qt.cTerminates rt.cTerminates
  | star rt => CTerminates.star rt.cTerminates
  | start => CTerminates.start
  | end' => CTerminates.end'
  | capture n rt => CTerminates.capture n rt.cTerminates

theorem allTerminates {r : Regex α} (hr : r.CRegularAnchor) :
  r.AllTerminates := hr.cTerminates.allTerminates

theorem terminatesEquiv {q r : Regex α}
    (hq : q.CRegularAnchor) (hr : r.CRegularAnchor) : q ≃ᵗᵉ r :=
  fun _ _ _ ↦
    ⟨fun _ ↦ hr.allTerminates _ _ _, fun _ ↦ hq.allTerminates _ _ _⟩

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
  | star r => ⟨_, star r.simpStartToBot.2⟩
  | start => ⟨_, bot⟩ -- here!
  | end' => ⟨_, end'⟩
  | capture n r => ⟨_, capture n r.simpStartToBot.2⟩

def HasStart {r : Regex α} (hr : r.CRegularAnchor) := match hr with
  | bot => False
  | empty => False
  | unit _ => False
  | concat q r => q.HasStart ∨ r.HasStart
  | or q r => q.HasStart ∨ r.HasStart
  | star r => r.HasStart
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
    (star_concat : {q r : Regex α} →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive hq → motive hr → motive (concat (star hq) hr))
    (start_concat : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (concat .start hr))
    (end'_concat : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (concat .end' hr))
    (capture_concat : {n : ℕ} → {q r : Regex α} →
      (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive (concat hq hr) → motive (concat (capture n hq) hr))
    (or : {q r : Regex α} → (hq : q.CRegularAnchor) → (hr : r.CRegularAnchor) →
      motive hq → motive hr → motive (or hq hr))
    (star : {r : Regex α} → (hr : r.CRegularAnchor) →
      motive hr → motive (star hr))
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
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .concat (.unit c) r => unit_concat c r
  | .concat (.concat p q) r => concat_concat p q r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      (.concat p (.concat q r)))
  | .concat (.or p q) r => or_concat p q r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      (.concat p r))
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      (.concat q r))
  | .concat (.star q) r => star_concat q r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      q) (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .concat .start r => start_concat r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .concat .end' r => end'_concat r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .concat (.capture n q) r => capture_concat q r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      (.concat q r))
  | .or q r => or q r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      q) (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .star r => star r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
  | .start => start
  | .end' => end'
  | .capture n r => capture n r
      (simpStartRec bot empty unit bot_concat empty_concat unit_concat concat_concat
      or_concat star_concat start_concat end'_concat capture_concat or star start end' capture
      r)
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
  | concat (star q) r => ⟨_, or r.simpStart.2 (concat q.simpStart.2
      (concat (star q.simpStartToBot.2) r.simpStartToBot.2))⟩
  | concat start r => ⟨_, r.simpStart.2⟩
  | concat end' r => ⟨_, concat end' r.simpStart.2⟩
  | concat (capture n q) r => (concat q r).simpStart
  | or q r => ⟨_, or q.simpStart.2 r.simpStart.2⟩
  | star r => ⟨_, or empty (concat r.simpStart.2 (star r.simpStartToBot.2))⟩
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

omit deq in
/-- `simpStart` removes all start anchors -/
theorem simpStart_noStart {r : Regex α} (hr : r.CRegularAnchor)
    : ¬hr.simpStart.2.HasStart := by
  induction hr using simpStartRec
  all_goals rw [simpStart.eq_def]; simp [HasStart, simpStartToBot_noStart, *]

/-- `simpStart` produces an equivalent language -/
theorem languageEquiv_simpStart {r : Regex α} (hr : r.CRegularAnchor)
    : r ≃ˡᵃ hr.simpStart.1 := by
  refine ⟨hr.terminatesEquiv hr.simpStart.2, ?_⟩
  induction hr using simpStartRec
  case bot | empty | unit _ | end' => simp [simpStart]
  case bot_concat r => simp [languageEquiv_bot_concat.2, simpStart]
  case empty_concat r => simp [languageEquiv_empty_concat.2, simpStart, r]
  case unit_concat c r => sorry
  case concat_concat p q r => simp [languageEquiv_concat_assoc.2, simpStart, r]
  case or_concat p q r => simp [languageEquiv_or_concat.2, simpStart, isMatch_or, q, r]
  case star_concat q r => sorry
  case start_concat r rind => simp [(languageEquiv_start_concat
    fun w s cap _ ↦ r.allTerminates w s cap).2, simpStart, rind]
  case end'_concat r rind => simp [(languageEquiv_end'_concat ⟨
    r.terminatesEquiv r.simpStart.2, rind⟩).2, simpStart]
  case capture_concat n q r => sorry
  case or q r => simp [simpStart, isMatch_or, q, r]
  case star r => simp [simpStart]; sorry
  case start => simp [simpStart, isMatch_start, isMatch_empty]
  case capture n r => simp [simpStart, isMatch_capture, r]

end CRegularAnchor

end Regex
