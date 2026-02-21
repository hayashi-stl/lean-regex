import Mathlib.Data.List.Monad
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Tactic
import Regex.Algorithm.PosTermination
import Regex.List

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w}

theorem StarType.map_match {α β : Type*} (f : α → β) (t : StarType) (g l : α)
    : f (match t with | .greedy => g | .lazy => l) =
      match t with | .greedy => f g | .lazy => f l := by rcases t <;> simp

theorem StarType.flatten_match {α : Type*} (t : StarType) (gg gl lg ll : α)
    : (match t with
        | .greedy => match t with | .greedy => gg | .lazy => gl
        | .lazy => match t with | .greedy => lg | .lazy => ll) =
      (match t with | .greedy => gg | .lazy => ll) := by rcases t <;> simp

--def isTerminating (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w) :=
--  (Action.regex r s cap).terminator.isSome

def initMatchPartial (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
    : MatchStack w where
  entries := [Action.regex r s cap]
  arg := []

/-- Whether a particular regex match terminates -/
def Terminates (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w) :=
  (r.initMatchPartial w s cap).Terminates

--omit deq in
--open MatchStack in
--theorem initMatchPartial_lawful : (r.initMatchPartial w s cap).Lawful := by
--  apply Lawful.mk
--  all_goals simp only [initMatchPartial]
--  · simp [posLawful_sorted]
--  · simp only [posLawful_lawful_actions, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
--    apply Action.Lawful.mk
--    simp [Action.posLawful_truth]
--  · simp only [posLawful_posLawArg_fst, List.cons.injEq, List.nil_eq, and_imp,
--      forall_eq_apply_imp_iff, forall_eq']
--    apply Action.LawfulArg.mk
--    all_goals simp [Action.posLawful_le_arg, Action.posLawful_lt_arg_filterEmpty]
--  · simp [posLawful_consecutive]

open MatchStack in
def matchPartial (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
  (term : r.Terminates w s cap)
    : PartialMatches w := T.run ⟨
      (r.initMatchPartial w s cap), term
    ⟩

open MatchStack in
theorem matchPartial_bot_terminates (s : Pos w) (cap : Captures w)
    : [/⊥/].Terminates w s cap := by
  apply terminates_of_stepN (n := 2) (mat := [])
  simp [stepN, step, initMatchPartial, Action.process, Except.ok_eq_pure]

open MatchStack in
theorem matchPartial_empty_terminates (s : Pos w) (cap : Captures w)
    : [//].Terminates w s cap := by
  apply terminates_of_stepN (n := 2) (mat := [(s, cap)])
  simp [stepN, step, initMatchPartial, Action.process, Except.ok_eq_pure]

open MatchStack in
theorem matchPartial_unit_terminates (c : α) (s : Pos w) (cap : Captures w)
    : [/c/].Terminates w s cap := by
  apply terminates_of_stepN (n := 2)
    (mat := if h : w[s.val]? = some c then [(s.succOfIndex h, cap)] else [])
  simp [stepN, step, initMatchPartial, Action.process, Except.ok_eq_pure]

open MatchStack in
theorem matchPartial_concat_terminates {q r : Regex α} {s : Pos w} {cap : Captures w}
    : [/⟨q⟩ ⟨r⟩/].Terminates w s cap ↔ ∃ term : q.Terminates w s cap,
      ∀ mat ∈ q.matchPartial w s cap term, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    have hst' : (mk [Action.regex [/⟨q⟩ ⟨r⟩/] s cap] []).step = ?_ := by
      simp only [step, Action.process, List.append_nil]; rfl
    have term' := step_terminates term hst'
    have qterm := top_terminates term' (by simp only; rw [← List.singleton_append])
    simp only at qterm
    use qterm
    intro mat qmat
    have run := top_run_terminates term'
    --have term'' := step_terminates' term'; simp [step] at term''
    --have term'' := step_terminates' term''; simp [step] at term''

open MatchStack in
theorem matchPartial_bot (s : Pos w) (cap : Captures w)
    : matchPartial [/⊥/] w s cap (matchPartial_bot_terminates s cap) = [] := by
  simp only [matchPartial, initMatchPartial]
  rw [T.run, T.step]
  simp only [step, Action.process, List.extract_eq_drop_take, ↓dreduceDIte,
    List.filter_nil, List.map_nil, List.nil_append]
  rw [T.run, T.step]
  simp [step]

open MatchStack in
theorem matchPartial_empty (s : Pos w) (cap : Captures w)
    : matchPartial [//] w s cap (matchPartial_empty_terminates s cap)
    = [(s, cap)] := by
  simp only [matchPartial, initMatchPartial]
  rw [T.run, T.step]
  simp only [step, Action.process, List.extract_eq_drop_take, ↓dreduceDIte,
    List.filter_nil, List.map_nil, List.nil_append]
  rw [T.run, T.step]
  simp [step]

open MatchStack in
theorem matchPartial_unit (c : α) (s : Pos w) (cap : Captures w)
    : matchPartial [/c/] w s cap (matchPartial_unit_terminates c s cap)
      = if h : w[s.val]? = some c then [(s.succOfIndex h, cap)] else [] := by
  simp only [matchPartial, initMatchPartial]
  rw [T.run, T.step]
  simp only [step, Action.process, List.extract_eq_drop_take, ↓dreduceDIte,
    List.filter_nil, List.map_nil, List.nil_append]
  rw [T.run, T.step]
  simp [step]

open MatchStack in
theorem matchPartial_concat (q r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/⟨q⟩ ⟨r⟩/].Terminates w s cap)
    : matchPartial [/⟨q⟩ ⟨r⟩/] w s cap term
      = q.matchPartial w s cap >>= fun (s', cap') ↦ r.matchPartial w s' cap' := by
  sorry

--theorem MatchStack.T.step_run {st st' : MatchStack.T w}
--    (hst : st.step = Except.ok st')
--    : st.run = st'.run := by

def match' (r : Regex α) (w : List α) (term : r.isTerminating w 0 0) :
  PartialMatches w := r.matchPartial w 0 0 term

#eval runMatch [/(1 ← 0 | 1)/] [0, 1, 2, 3] 100

mutual
--def matchPartialStar (t : StarType) (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
--    : List (IccFrom s × Captures w) :=
--  matchPartial r w s cap >>=
--  /- Matching an empty string means you can't continue -/
--    fun (s', cap') ↦ if s.val = s'.val then pure (s', cap') else
--      (fun (s'', cap'') ↦ (s'.widenLeft s'', cap'')) <$>
--      matchPartial (star t r) w s'.expandZero cap'
--termination_by (star t r, s.distToEnd, 0)
--decreasing_by
--  · simp only [Prod.lex_def, star.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_irrefl,
--      Nat.not_lt_zero, and_false, or_self, or_false]
--    exact Nat.lt_add_right (sizeOf t) Nat.zero_lt_one
--  · rename_i hs
--    simp only [Prod.lex_def, star.sizeOf_spec, Nat.lt_irrefl, Nat.not_lt_zero, and_false,
--      or_false, true_and, false_or]
--    apply Icc.distToEnd_lt
--    rcases lt_or_eq_of_le s'.is_ge with slt | seq
--    · exact slt
--    · contradiction

/-- Partial match: takes a regex, a string, a start position, and a list of
current captures, and returns a list of possible matches to check in order.
Each match is an end position combined with a capture list. -/
partial def matchPartial (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
    : List (IccFrom s × Captures w) :=
  match r with
  | bot => failure
  | empty => pure (s.iccFrom, cap)
  | unit c => if hs : w[s.val]? = c then pure (Icc.succOfIndex hs, cap) else failure
  | concat q r => do
      let (s', cap') ← q.matchPartial w s cap
      let (s'', cap'') ← r.matchPartial w s'.expandZero cap'
      pure (s'.widenLeft s'', cap'')
  | or q r => q.matchPartial w s cap ++ r.matchPartial w s cap
  | filterEmpty emp r => do
      let (s', cap') ← r.matchPartial w s cap
      if (s'.val = s.val) = emp then pure (s', cap') else failure
  --| star t r => match t with
  --  | .greedy => matchPartialStar .greedy r w s cap ++ pure (s.iccFrom, cap)
  --  | .lazy => pure (s.iccFrom, cap) ++ matchPartialStar .lazy r w s cap
  | star t r => match t with
    | .greedy => matchPartial [/(¥ᵣ(r) •ε | (¥ᵣ(r) -ε) ¥ᵣ(r)*) | ε/] w s cap
    | .lazy => matchPartial [/ε | (¥ᵣ(r) •ε | (¥ᵣ(r) -ε) ¥ᵣ(r)*?)/] w s cap
  | capture n r => do
      let (s', cap') ← r.matchPartial w s cap
      pure (s', cap'.update n (pure ⟨s, s'⟩))
  | backref d n => do
      let ⟨cs, ct⟩ ← if let some w' := (cap n).getLast? then pure w'
        else return (← matchPartial d w s cap)
      if h : w.extract s.val (s.val + (ct.val - cs.val)) = w.extract cs.val ct.val then
        pure (Icc.addOfIndex h (length_extract_pos_posFrom cs ct), cap) else failure
--termination_by (s.distToEnd, r.numRawStars, r)
--decreasing_by
--  all_goals have sizelt (a b : ℕ) : a < 1 + a + b := by linarith
--  all_goals have zz (n : ℕ) : 0 < n ∨ n = 0 := by omega
--  any_goals simp [Prod.lex_def, numRawStars, sizelt, ← le_iff_lt_or_eq, zz]
end

theorem matchPartial_bot (w : List α) (s : Pos w) (cap : Captures w)
    : matchPartial [/⊥/] w s cap = [] := by
  simp [matchPartial, failure]

theorem matchPartial_empty (w : List α) (s : Pos w) (cap : Captures w)
    : matchPartial [//] w s cap = [(s.iccFrom, cap)] := by
  simp [matchPartial]

--theorem matchPartial_star_nil (t : StarType) (r : Regex α) (s : Pos []) (cap : Captures [])
--    : Prod.fst <$> (star t r).matchPartial [] s cap =
--      if matchPartial r [] s cap = [] then [s.posFrom] else [s.posFrom, s.posFrom] := by
--  rcases t
--  · simp only [matchPartial, List.pure_def, List.cons_append, List.nil_append,
--      List.map_eq_map, List.map_cons]
--    simp only [matchPartialStar, Prod.mk.eta, List.pure_def, List.map_eq_map,
--      List.bind_eq_flatMap]
--    split_ifs with h
--    · simp [h]
--    ·

/-- A finishing partial match -/
def matchFinish (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
    : Option (Captures w) :=
  Prod.snd <$> (matchPartial r w s cap).find? fun (s, _) ↦ s = s.end'

/-- Matches a regex against an entire string.
Returns a list of captures if it succeeds.
Called `match'` because `match` is a keyword. -/
def match' (r : Regex α) (w : List α) : Option (Captures w) := matchFinish r w 0 0
  --Prod.snd <$> (matchPartial r w 0 0).find? fun (s, _) ↦ s = Pos.end'

theorem match'_bot (w : List α) : match' [/⊥/] w = none := by
  simp [match', matchFinish, matchPartial_bot]

theorem match'_empty (w : List α) : match' [//] w = if w = [] then some 0 else none := by
  simp only [match', matchFinish, matchPartial_empty, List.find?_singleton,
    decide_eq_true_eq, Option.map_eq_map, Option.map_if]
  congr
  rw [Icc.zero_end']
  rfl

theorem match'_unit (c : α) (w : List α)
    : match' [/c/] w = if w = [c] then some 0 else none := by
  simp only [match', matchFinish, matchPartial, List.pure_def, Option.map_eq_map]
  split_ifs with w0c wc wc
  · simp only [List.find?_singleton, decide_eq_true_eq, Option.map_if,
      ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
    rw [← Subtype.val_inj]
    simp [Icc.succOfIndex, wc]
  · simp only [List.find?_singleton, decide_eq_true_eq, Option.map_if, ite_eq_right_iff,
      reduceCtorEq, imp_false]
    contrapose! wc
    apply_fun Subtype.val at wc
    simp only [Icc.zero_val, Icc.succOfIndex_val, zero_add, Icc.end'_val] at wc
    rw [Icc.zero_val] at w0c
    rw [eq_comm, List.length_eq_one_iff] at wc
    rcases wc with ⟨a, wa⟩
    have wa' := congrArg (·[0]?) wa
    simp only [w0c, List.length_cons, List.length_nil, zero_add, zero_lt_one,
      getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at wa'
    exact wa' ▸ wa
  · simp [wc] at w0c
  · simp [failure]

theorem match'_concat (q r : Regex α) (w : List α)
    : match' [/¥ᵣ(q)¥ᵣ(r)/] w = (matchPartial q w 0 0).findSome?
        (fun (s, cap) ↦ matchFinish r w s cap) := by
  simp only [match', matchFinish, matchPartial, List.pure_def, List.bind_eq_flatMap,
    List.find?_flatMap, List.find?_singleton, decide_eq_true_eq, Option.map_eq_map,
    List.map_findSome?]
  congr
  rw [Function.comp_def]
  ext x cs
  rw [Option.map_eq_some_iff, Option.map_eq_some_iff]
  simp only [Prod.exists, exists_eq_right]
  simp only [List.findSome?_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
    Prod.mk.injEq, ite_eq_right_iff, reduceCtorEq, imp_false, Prod.forall,
    exists_and_right, Prod.exists, ↓existsAndEq, and_true]
  rw [exists_comm]
  apply exists_congr; intro s
  simp only [List.find?_eq_some_iff_append, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Prod.forall, exists_and_right,
    ← Icc.val_inj]
  rw [← exists_and_left]
  apply exists_congr; intro csl
  rw [and_left_comm]
  rfl

theorem match'_or (q r : Regex α) (w : List α)
    : match' (or q r) w = (match' q w <|> match' r w) := by
  simp only [match', matchFinish, matchPartial, List.find?_append, Option.map_eq_map,
    Option.orElse_eq_orElse, Option.orElse_eq_or]
  rw [Option.map_or]

/-- Matching specialized to strings. -/
def matchStr (r : Regex Char) (w : String) := match' r w.toList

def isMatch (r : Regex α) (w : List α) := ∃ cs, match' r w = some cs

theorem isMatch_bot (w : List α) : ¬isMatch [/⊥/] w := by
  simp [isMatch, match'_bot]

theorem isMatch_empty (w : List α) : isMatch [//] w ↔ w = [] := by
  simp [isMatch, match'_empty]

theorem isMatch_unit (c : α) (w : List α) : isMatch [/c/] w ↔ w = [c] := by
  simp [isMatch, match'_unit]

theorem isMatch_or (q r : Regex α) (w : List α)
    : isMatch (or q r) w ↔ isMatch q w ∨ isMatch r w := by
  simp only [isMatch, match'_or, Option.orElse_eq_orElse, Option.orElse_eq_or,
    Option.or_eq_some_iff]
  constructor <;> intro excs
  · rcases excs with ⟨cs, qcs | ⟨q0, rcs⟩⟩
    · exact Or.inl ⟨cs, qcs⟩
    · exact Or.inr ⟨cs, rcs⟩
  · by_cases qcs : ∃ cs, q.match' w = some cs
    · rcases qcs with ⟨cs, qcs⟩
      exact ⟨cs, Or.inl qcs⟩
    · simp only [qcs, false_or] at excs
      push_neg at qcs
      rw [← Option.eq_none_iff_forall_ne_some] at qcs
      rcases excs with ⟨cs, rcs⟩
      exact ⟨cs, Or.inr ⟨qcs, rcs⟩⟩

def language (r : Regex α) : Language α := {w | isMatch r w}

theorem language_bot (α : Type*) [DecidableEq α] : ([/⊥/] : Regex α).language = 0 := by
  simp [language, isMatch_bot]
  rfl

theorem language_empty (α : Type*) [DecidableEq α] : ([//] : Regex α).language = {[]} := by
  simp [language, isMatch_empty]

theorem language_unit (c : α) : [/c/].language = {[c]} := by
  simp [language, isMatch_unit]

theorem language_or (q r : Regex α) : (or q r).language = q.language + r.language := by
  simp [language, isMatch_or, Language.add_def, Set.union_def]

#eval matchStr [/(1 ← ('0' | '1')*) \⊥1/] "011011"

end Regex
