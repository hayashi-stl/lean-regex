import Regex.Parse

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

inductive Action {α : Type u} (w : List α) : Type u where
  | regex (r : Regex α) (s : Pos w) (cap : Captures w) : Action w
  | concatWait (q : Regex α) (r : Regex α) (s : Pos w) : Action w
  | concat (r : Regex α) (s : Pos w) (old new : PartialMatches w) : Action w
  | orWait (r : Regex α) (s : Pos w) (cap : Captures w) : Action w
  | or (s : Pos w) (fst : PartialMatches w) : Action w
  | filterEmpty (emp : Bool) (s : Pos w) : Action w
  | capture (n : ℕ) (s : Pos w) : Action w
  deriving Repr

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
    | .concat q r => ⟨[regex q s cap, concatWait q r s], []⟩
    | .or q r => ⟨[regex q s cap, orWait r s cap], []⟩
    | .filterEmpty emp r => ⟨[regex r s cap, filterEmpty emp s], []⟩
    | .star t r => match t with
      | .greedy => ⟨[regex [/(⟨r⟩ •ε | (⟨r⟩ -ε)⟨r⟩*) | ε/] s cap], []⟩
      | .lazy => ⟨[regex [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε)⟨r⟩*)/] s cap], []⟩
    | .start => ⟨[], if s = 0 then [(s, cap)] else []⟩
    | .end' => ⟨[], if s = s.end' then [(s, cap)] else []⟩
    | .capture n r => ⟨[regex r s cap, capture n s], []⟩
    | .backref d n => ⟨[regex (match (cap n).getLast? with
      | none => match d with | .bot => [/⊥/] | .empty => [//]
      | some (cs, ct) => list (w.extract cs.val ct.val)
      ) s cap], []⟩
  | .concatWait _ r _ => ⟨if h : arg = []
    then []
    else [concat r ((arg.map Prod.fst).min
      (by contrapose! h; exact List.map_eq_nil_iff.mp h)) arg []], []⟩
  | .concat r s old new => match old with
    | [] => ⟨[], new ++ arg⟩
    | (s', cap) :: old => ⟨[regex r s' cap, concat r s old (new ++ arg)], []⟩
  | .orWait r s cap => ⟨[regex r s cap, or s arg], []⟩
  | .or _ fst => ⟨[], fst ++ arg⟩
  | .filterEmpty emp s => ⟨[], arg.filter fun (s', _) ↦ (s = s') = emp⟩
  | .capture n s => ⟨[], arg.map fun (s', cap) ↦
      (s', cap.update n [(s, s')])⟩

def Action.pos (ac : Action w) : Pos w := match ac with
  | .regex _ s _ => s
  | .concatWait _ _ s => s
  | .concat _ s _ _ => s
  | .orWait _ s _ => s
  | .or s _ => s
  | .filterEmpty _ s => s
  | .capture _ s => s

def StepResult (w : List α) := Except (PartialMatches w) (MatchStack w)

def Action.matchStack (ac : Action w) (arg : PartialMatches w)
    : MatchStack w := MatchStack.mk [ac] arg

namespace MatchStack

/-- Advancing the state of the regex matches. The state steps successfully
unless the stack is empty, in which case the list of matches is returned -/
def step (st : MatchStack w) : StepResult w
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
