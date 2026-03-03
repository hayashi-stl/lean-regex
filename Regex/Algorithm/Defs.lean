import Regex.Parse

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

/-- Various actions the match stack can execute -/
inductive Action (w : List α) : Type u where
  /-- Start a regex match (and maybe finish it). -/
  | regex (r : Regex α) (s : Pos w) (cap : Captures w) : Action w
  /-- Wait for matches from the first regex of a concatenation -/
  | concatWait (r : Regex α) : Action w
  /-- Process the second regex with another match -/
  | concat (r : Regex α) (old new : PartialMatches w) : Action w
  /-- Wait for matches from the first regex of an alternation -/
  | orWait (r : Regex α) (s : Pos w) (cap : Captures w) : Action w
  /-- Concatenate the two lists of matches -/
  | or (fst : PartialMatches w) : Action w
  /-- Wait for matches from the first match attempt of a star -/
  | starWait (r : Regex α) (s : Pos w) (cap : Captures w): Action w
  /-- Process the star with another match. This looks like `concat`,
  but has special behavior that it's not worth complicating `concat` for. -/
  | star (r : Regex α) (s : Pos w)
    (cap : Captures w) (old new : PartialMatches w) : Action w
  /-- Capture a match -/
  | capture (n : ℕ) (s : Pos w) : Action w
  deriving Repr

/-- A stack of actions, along with an argument -/
@[ext]
structure MatchStack (w : List α) where
  entries : List (Action w)
  arg : PartialMatches w
  deriving Repr

def Action.process (ac : Action w) (arg : PartialMatches w)
    : MatchStack w := match ac with
  | Action.regex r s cap => match r with
    | .bot => ⟨[], []⟩
    | .empty => ⟨[], [(s, cap)]⟩
    | .unit c => ⟨[], if h : w[s.val]? = c then [(s.succOfIndex h, cap)] else []⟩
    | .concat q r => ⟨[regex q s cap, concatWait r], []⟩
    | .or q r => ⟨[regex q s cap, orWait r s cap], []⟩
    | .star r => ⟨[regex r s cap, starWait r s cap], []⟩
    | .start => ⟨[], if s = 0 then [(s, cap)] else []⟩
    | .end' => ⟨[], if s = w.length then [(s, cap)] else []⟩
    | .capture n r => ⟨[regex r s cap, capture n s], []⟩
    | .backref d n => ⟨[regex (match (cap n).head? with
      | none => match d with | .bot => [/⊥/] | .empty => [//]
      | some (cs, ct) => list (w.extract cs ct)
      ) s cap], []⟩
  | .concatWait r => ⟨[concat r arg []], []⟩
  | .concat r old new => match old with
    | [] => ⟨[], new ++ arg⟩
    | (s', cap) :: old => ⟨[regex r s' cap, concat r old (new ++ arg)], []⟩
  | .orWait r s cap => ⟨[regex r s cap, or arg], []⟩
  | .or fst => ⟨[], fst ++ arg⟩
  | .starWait r s cap => ⟨[star r s cap arg []], []⟩
  | .star r s cap old new => match old with
    | [] => ⟨[], new ++ arg ++ [(s, cap)]⟩
    | (s', cap') :: old => ⟨if s < s'
        then [regex [/⟨r⟩*/] s' cap', star r s cap old (new ++ arg)]
        else [star r s cap old (new ++ arg ++ [(s', cap')])], []⟩
  | .capture n s => ⟨[], arg.map fun (s', cap) ↦
      (s', cap.update n [(s, s')])⟩

--/-- The position associated with an action. Used for position lawfulness proofs -/
--def Action.pos (ac : Action α) : ℕ := match ac with
--  | .regex _ _ s _ => s
--  | .concatWait _ _ _ s => s
--  | .concat _ _ s _ _ => s
--  | .orWait _ _ s _ => s
--  | .or s _ => s
--  | .filterEmpty _ s => s
--  | .capture _ s => s

-- Apparently without the dependent argument `w`, the type checker doesn't
-- realize that `StepResult α` is a monad on `MatchStack α` and won't
-- let `bind` through

/-- The result of stepping the match stack. Either the next state or the
match result -/
def StepResult (w : List α) := Except (PartialMatches w)
  deriving Monad, LawfulMonad

/-- Constructs a match stack out of a single action -/
def Action.matchStack (ac : Action w) (arg : PartialMatches w)
    : MatchStack w := MatchStack.mk [ac] arg

namespace MatchStack

/-- Advancing the state of the regex matches. The state steps successfully
unless the stack is empty, in which case the list of matches is returned -/
def step (st : MatchStack w) : StepResult w (MatchStack w)
  := match st.entries with
  | [] => Except.error st.arg
  | action :: stack => let ⟨entries, return'⟩ := action.process st.arg
    Except.ok ⟨entries ++ stack, return'⟩

theorem step_eq_ok {st st' : MatchStack w} (hst : st.step = Except.ok st')
    : ∃ (ac : Action w) (as : List (Action w)), st.entries = ac :: as ∧ st' = MatchStack.mk
        (entries := (ac.process st.arg).entries ++ as)
        (arg := (ac.process st.arg).arg)
        := by
  simp only [step] at hst
  split at hst <;> try simp at hst
  rename_i as ac as' has
  rw [Except.ok.injEq] at hst
  exact ⟨ac, as', has, Eq.symm hst⟩

theorem step_eq_error {st : MatchStack w} {mat : PartialMatches w}
    (hst : st.step = Except.error mat)
    : st.entries = [] := by
  rw [step] at hst; split at hst <;> first | assumption | simp at hst

theorem step_eq_error_iff {st : MatchStack w}
    : st.step = Except.error st.arg ↔ st.entries = [] := by
  constructor
  · exact fun hst ↦ st.step_eq_error hst
  · intro hst
    rw [step, hst]

theorem step_singleton (ac : Action w) (arg : PartialMatches w)
    : (MatchStack.mk [ac] arg).step = Except.ok (ac.process arg) := by
  simp [step]

end MatchStack

end Regex
