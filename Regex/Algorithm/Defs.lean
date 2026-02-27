import Regex.Parse

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α}

/-- Various actions the match stack can execute -/
inductive Action (α : Type u) : Type u where
  /-- Start a regex match (and maybe finish it). -/
  | regex (r : Regex α) (w : List α) (s : ℕ) (cap : Captures) : Action α
  /-- Wait for matches from the first regex of a concatenation -/
  | concatWait (r : Regex α) (w : List α) : Action α
  /-- Process the second regex with another match -/
  | concat (r : Regex α) (w : List α) (old new : PartialMatches) : Action α
  /-- Wait for matches from the first regex of an alternation -/
  | orWait (r : Regex α) (w : List α) (s : ℕ) (cap : Captures) : Action α
  /-- Concatenate the two lists of matches -/
  | or (fst : PartialMatches) : Action α
  /-- Wait for matches from the first match attempt of a star -/
  | starWait (t : StarType) (r : Regex α) (w : List α) (s : ℕ) (cap : Captures): Action α
  /-- Process the star with another match. This looks like `concat`,
  but has special behavior that it's not worth complicating `concat` for. -/
  | star (t : StarType) (r : Regex α) (w : List α) (s : ℕ) (cap : Captures)
    (old new : PartialMatches) : Action α
  /-- Capture a match -/
  | capture (n : ℕ) (s : ℕ) : Action α
  deriving Repr

/-- A stack of actions, along with an argument -/
@[ext]
structure MatchStack (α : Type*) where
  entries : List (Action α)
  arg : PartialMatches
  deriving Repr

def Action.process (ac : Action α) (arg : PartialMatches)
    : MatchStack α := match ac with
  | Action.regex r w s cap => match r with
    | .bot => ⟨[], []⟩
    | .empty => ⟨[], [(s, cap)]⟩
    | .unit c => ⟨[], if h : w[s]? = c then [(s + 1, cap)] else []⟩
    | .concat q r => ⟨[regex q w s cap, concatWait r w], []⟩
    | .or q r => ⟨[regex q w s cap, orWait r w s cap], []⟩
    | .star t r => ⟨[regex r w s cap, starWait t r w s cap], []⟩
    | .start => ⟨[], if s = 0 then [(s, cap)] else []⟩
    | .end' => ⟨[], if s = w.length then [(s, cap)] else []⟩
    | .capture n r => ⟨[regex r w s cap, capture n s], []⟩
    | .backref d n => ⟨[regex (match (cap n).head? with
      | none => match d with | .bot => [/⊥/] | .empty => [//]
      | some (cs, ct) => list (w.extract cs ct)
      ) w s cap], []⟩
  | .concatWait r w => ⟨[concat r w arg []], []⟩
  | .concat r w old new => match old with
    | [] => ⟨[], new ++ arg⟩
    | (s', cap) :: old => ⟨[regex r w s' cap, concat r w old (new ++ arg)], []⟩
  | .orWait r w s cap => ⟨[regex r w s cap, or arg], []⟩
  | .or fst => ⟨[], fst ++ arg⟩
  | .starWait t r w s cap => ⟨[star t r w s cap arg []], []⟩
  | .star t r w s cap old new => match old with
    | [] => ⟨[], match t with
        | .greedy => new ++ arg ++ [(s, cap)]
        | .lazy => [(s, cap)] ++ new ++ arg⟩
    | (s', cap) :: old => ⟨if s < s'
        then [regex [/⟨r⟩*‹t›/] w s' cap, star t r w s cap old (new ++ arg)]
        else [star t r w s cap old (new ++ arg ++ [(s', cap)])], []⟩
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
def StepResult := Except PartialMatches
  deriving Monad, LawfulMonad

/-- Constructs a match stack out of a single action -/
def Action.matchStack (ac : Action α) (arg : PartialMatches)
    : MatchStack α := MatchStack.mk [ac] arg

namespace MatchStack

/-- Advancing the state of the regex matches. The state steps successfully
unless the stack is empty, in which case the list of matches is returned -/
def step (st : MatchStack α) : StepResult (MatchStack α)
  := match st.entries with
  | [] => Except.error st.arg
  | action :: stack => let ⟨entries, return'⟩ := action.process st.arg
    Except.ok ⟨entries ++ stack, return'⟩

theorem step_eq_ok {st st' : MatchStack α} (hst : st.step = Except.ok st')
    : ∃ (ac : Action α) (as : List (Action α)), st.entries = ac :: as ∧ st' = MatchStack.mk
        (entries := (ac.process st.arg).entries ++ as)
        (arg := (ac.process st.arg).arg)
        := by
  simp only [step] at hst
  split at hst <;> try simp at hst
  rename_i as ac as' has
  rw [Except.ok.injEq] at hst
  exact ⟨ac, as', has, Eq.symm hst⟩

theorem step_eq_error {st : MatchStack α} {mat : PartialMatches}
    (hst : st.step = Except.error mat)
    : st.entries = [] := by
  rw [step] at hst; split at hst <;> first | assumption | simp at hst

theorem step_eq_error_iff {st : MatchStack α}
    : st.step = Except.error st.arg ↔ st.entries = [] := by
  constructor
  · exact fun hst ↦ st.step_eq_error hst
  · intro hst
    rw [step, hst]

theorem step_singleton (ac : Action α) (arg : PartialMatches)
    : (MatchStack.mk [ac] arg).step = Except.ok (ac.process arg) := by
  simp [step]

end MatchStack

end Regex
