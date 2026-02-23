import Mathlib.Data.List.Monad
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Tactic
import Regex.Algorithm.Termination
import Regex.List
import Regex.Util

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

/-! Some tactics for proving termination -/

section Tactic

open Lean Parser Tactic

syntax stepArgs :=
  (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (location)?

/-- Steps a match stack -/
syntax "step" stepArgs : tactic
syntax "step" stepArgs : conv

macro_rules
| `(tactic| step only $[[$args,*]]? $[$pos:location]?) => `(tactic|
  (first
  | rw [MatchStack.step_terminates_iff, MatchStack.Terminates'.eq_def] $[$pos]?
  | rw [MatchStack.run_eq_step_run] $[$pos]?);
  simp only [MatchStack.step, Action.process] $[$pos]?;
  try simp only $[[$args,*]]? $[$pos]?)
| `(tactic| step $[[$args,*]]? $[$pos:location]?) => `(tactic|
  (first
  | rw [MatchStack.step_terminates_iff, MatchStack.Terminates'.eq_def] $[$pos]?
  | rw [MatchStack.run_eq_step_run] $[$pos]?);
  simp only [MatchStack.step, Action.process] $[$pos]?;
  try simp $[[$args,*]]? $[$pos]?)
| `(tactic| step only $[[$args,*]]?) => `(tactic| step only $[[$args,*]]? at ⊢)
| `(tactic| step $[[$args,*]]?) => `(tactic| step $[[$args,*]]? at ⊢)

macro_rules
| `(conv| step only $[[$args,*]]?) => `(conv|
  (first
  | rw [MatchStack.step_terminates_iff, MatchStack.Terminates'.eq_def]
  | rw [MatchStack.run_eq_step_run]) <;>
  simp only [MatchStack.step, Action.process] <;>
  try simp only $[[$args,*]]?)
| `(conv| step $[[$args,*]]?) => `(conv|
  (first
  | rw [MatchStack.step_terminates_iff, MatchStack.Terminates'.eq_def]
  | rw [MatchStack.run_eq_step_run]) <;>
  simp only [MatchStack.step, Action.process] <;>
  try simp $[[$args,*]]?)

/-- Runs the top action of a match stack -/
syntax "run_top" (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" at " term (" with " ident ident)?)? : tactic
syntax "run_top" (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  " using " term : tactic

macro_rules
| `(tactic| run_top only $[[$args,*]]? at $pos:term with $a:ident $b:ident) => `(tactic|
    rw [MatchStack.top_run_terminates_iff (by simp only; rfl)] at $pos:term;
    have tmp := $pos;
    clear $pos:term;
    have ⟨$a, $b⟩ := tmp;
    clear tmp;
    simp only $[[$args,*]]? at $a $b;
  )
| `(tactic| run_top only $[[$args,*]]? $[at $pos:term]?) => `(tactic|
    (first
    | rw [MatchStack.top_run_terminates_iff (by simp only; rfl)] $[at $pos:term]?
    | rw [run_eq_top_run (by simp only; rfl)] $[at $pos:term]?);
    simp only $[[$args,*]]? $[at $pos:term]?
)
| `(tactic| run_top only $[[$args,*]]? using $pos:term) => `(tactic|
    rw [MatchStack.top_run_terminates_iff (by simp only; rfl)];
    use $pos:term;
    simp only $[[$args,*]]?
  )
| `(tactic| run_top $[[$args,*]]? at $pos:term with $a:ident $b:ident) => `(tactic|
    rw [MatchStack.top_run_terminates_iff (by simp only; rfl)] at $pos:term;
    have tmp := $pos;
    clear $pos:term;
    have ⟨$a, $b⟩ := tmp;
    clear tmp;
    simp $[[$args,*]]? at $a $b;
  )
| `(tactic| run_top $[[$args,*]]? $[at $pos:term]?) => `(tactic|
    (first
    | rw [MatchStack.top_run_terminates_iff (by simp only; rfl)] $[at $pos:term]?
    | rw [MatchStack.run_eq_top_run (by simp only; rfl)] $[at $pos:term]?);
    simp $[[$args,*]]? $[at $pos:term]?
)
| `(tactic| run_top $[[$args,*]]? using $pos:term) => `(tactic|
    rw [MatchStack.top_run_terminates_iff (by simp only; rfl)];
    use $pos:term;
    simp $[[$args,*]]?
  )

syntax "run_top!" (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  (" at " term (" with " ident ident)?)? : tactic
syntax "run_top!" (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")?
  " using " term  : tactic

macro_rules
| `(tactic| run_top! only $[[$args,*]]? at $pos:term with $a:ident $b:ident) => `(tactic|
    rw! [← List.singleton_append] at $pos:term;
    run_top only $[[$args,*]]? at $pos with $a $b
  )
| `(tactic| run_top! only $[[$args,*]]? $[at $pos:term]?) => `(tactic|
    rw! [← List.singleton_append] $[at $pos:term]?;
    run_top only $[[$args,*]]? $[at $pos]?
  )
| `(tactic| run_top! only $[[$args,*]]? using $pos:term) => `(tactic|
    rw! [← List.singleton_append];
    run_top only $[[$args,*]]? using $pos
  )
| `(tactic| run_top! $[[$args,*]]? at $pos:term with $a:ident $b:ident) => `(tactic|
    rw! [← List.singleton_append] at $pos:term;
    run_top $[[$args,*]]? at $pos with $a $b
  )
| `(tactic| run_top! $[[$args,*]]? $[at $pos:term]?) => `(tactic|
    rw! [← List.singleton_append] $[at $pos:term]?;
    run_top $[[$args,*]]? $[at $pos]?
  )
| `(tactic| run_top! $[[$args,*]]? using $pos:term) => `(tactic|
    rw! [← List.singleton_append];
    run_top $[[$args,*]]? using $pos
  )

end Tactic

--omit deq in
----theorem initMatchPartial_lawful : (r.initMatchPartial w s cap).Lawful := by
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

section MatchPartial
open MatchStack

def matchPartial (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
  (term : r.Terminates w s cap)
    : PartialMatches w := (r.initMatchPartial w s cap).run term

theorem matchPartial_terminates_iff {r : Regex α} {w : List α} {s : Pos w} {cap : Captures w}
    : r.Terminates w s cap ↔ (mk [.regex r s cap] []).Terminates := iff_of_eq rfl

theorem matchPartial_eq_run {r : Regex α} {w : List α} {s : Pos w} {cap : Captures w}
  {term : r.Terminates w s cap}
    : r.matchPartial w s cap term = (mk [.regex r s cap] []).run term := rfl

/-- `bot` always terminates -/
theorem bot_terminates {s : Pos w} {cap : Captures w}
    : [/⊥/].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

/-- `empty` always terminates -/
theorem empty_terminates {s : Pos w} {cap : Captures w}
    : [//].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

/-- `unit` always terminates -/
theorem unit_terminates {c : α} {s : Pos w} {cap : Captures w}
    : [/c/].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

theorem Action.concat_terminates {r : Regex α} {s : Pos w}
    {old new arg : PartialMatches w}
    : (MatchStack.mk [concat r s old new] arg).Terminates ↔
      ∀ mat ∈ old, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term mat mem
    induction old generalizing s new arg with | nil => contradiction | cons ent mat' ind =>
      step at term
      run_top! at term with term' term
      rw [List.mem_cons] at mem
      rcases mem with mem | mem
      · exact mem ▸ term'
      · exact ind term mem
  · intro term
    induction old generalizing s new arg with | nil => step; step | cons ent mat' ind =>
      step
      run_top!
      use term ent List.mem_cons_self
      exact ind fun m mem ↦ term _ (List.mem_cons_of_mem _ mem)

theorem Action.concatWait_terminates {q r : Regex α} {s : Pos w} {arg : PartialMatches w}
    : (MatchStack.mk [concatWait q r s] arg).Terminates ↔
      ∀ mat ∈ arg, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term mat mem
    step at term
    cases arg with | nil => contradiction | cons ent mat' =>
      simp only [reduceCtorEq, ↓reduceDIte, List.map_cons] at term
      rw [concat_terminates] at term
      exact term mat mem
  · intro term
    step
    cases arg with | nil => step | cons ent mat' =>
      simp only [reduceCtorEq, ↓reduceDIte, List.map_cons]
      rwa [concat_terminates]

/-- `concat q r` terminates iff `q` terminates and `r` terminates for every
end position and match provided by `q` -/
theorem concat_terminates {q r : Regex α} {s : Pos w} {cap : Captures w}
    : [/⟨q⟩ ⟨r⟩/].Terminates w s cap ↔ (term : q.Terminates w s cap) ∧
      ∀ mat ∈ q.matchPartial w s cap term, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term with term' term
    use term'
    intro mat qmat
    rw [matchPartial] at qmat
    rw [Action.concatWait_terminates] at term
    exact term mat qmat
  · rintro ⟨qterm, term⟩
    rw [Terminates, initMatchPartial] at ⊢
    step
    run_top! using qterm
    rw [Action.concatWait_terminates]
    exact fun mat run ↦ term mat run

theorem Action.or_terminates {s : Pos w} {fst arg : PartialMatches w}
    : (MatchStack.mk [or s fst] arg).Terminates := by step; step

theorem Action.orWait_terminates {r : Regex α} {s : Pos w} {cap : Captures w}
    {arg : PartialMatches w}
    : (MatchStack.mk [orWait r s cap] arg).Terminates ↔ r.Terminates w s cap := by
  constructor
  · intro term
    step at term
    run_top! at term with term' term
    exact term'
  · intro term
    step
    run_top! using term
    exact or_terminates

/-- `or q r` terminates iff `q` terminates and `r` terminates -/
theorem or_terminates {q r : Regex α} {s : Pos w} {cap : Captures w}
    : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap ↔
      q.Terminates w s cap ∧ r.Terminates w s cap := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term with term' term
    exact ⟨term', Action.orWait_terminates.mp term⟩
  · rintro ⟨qterm, rterm⟩
    rw [Terminates, initMatchPartial]
    step
    run_top! using qterm
    exact Action.orWait_terminates.mpr rterm

theorem Action.filterEmpty_terminates {emp : Bool} {s : Pos w} {arg : PartialMatches w}
    : (MatchStack.mk [filterEmpty emp s] arg).Terminates := by step; step

/-- `filterEmpty emp r` terminates iff `r` terminates -/
theorem filterEmpty_terminates {emp : Bool} {r : Regex α}
    {s : Pos w} {cap : Captures w}
    : [/⟨r⟩ ‹emp›ε/].Terminates w s cap ↔ r.Terminates w s cap := by
  constructor <;> intro term
  · rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term
    exact term.1
  · rw [Terminates, initMatchPartial]
    step
    run_top!
    exact ⟨term, Action.filterEmpty_terminates⟩

/-- `start` always terminates -/
theorem start_terminates {s : Pos w} {cap : Captures w}
    : [/⊢/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

/-- `end'` always terminates -/
theorem end'_terminates {s : Pos w} {cap : Captures w}
    : [/⊣/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

theorem Action.capture_terminates {n : ℕ} {s : Pos w} {arg : PartialMatches w}
    : (MatchStack.mk [capture n s] arg).Terminates := by step; step

/-- `capture emp r` terminates iff `r` terminates -/
theorem capture_terminates {n : ℕ} {r : Regex α}
    {s : Pos w} {cap : Captures w}
    : [/(‹n› ⟨r⟩)/].Terminates w s cap ↔ r.Terminates w s cap := by
  constructor <;> intro term
  · rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term
    exact term.1
  · rw [Terminates, initMatchPartial]
    step
    run_top!
    exact ⟨term, Action.capture_terminates⟩

theorem matchPartial_bot (s : Pos w) (cap : Captures w)
    : matchPartial [/⊥/] w s cap bot_terminates = [] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_empty (s : Pos w) (cap : Captures w)
    : matchPartial [//] w s cap empty_terminates
    = [(s, cap)] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_unit (c : α) (s : Pos w) (cap : Captures w)
    : matchPartial [/c/] w s cap unit_terminates
      = if h : w[s.val]? = some c then [(s.succOfIndex h, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.concat_run {r : Regex α} {s : Pos w} {old new arg : PartialMatches w}
    (term : ∀ mat ∈ old, r.Terminates w mat.1 mat.2)
    : (mk [.concat r s old new] arg).run (concat_terminates.mpr term)
      = new ++ arg ++
      (old.pmap (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt) term).flatten := by
  induction old generalizing new arg with | nil => step; step | cons ent mat ind =>
    simp only [List.mem_cons, forall_eq_or_imp, List.pmap_cons,
      List.flatten_cons] at term ⊢
    step
    run_top!
    rw [ind term.2]
    simp only [List.append_assoc, List.append_cancel_left_eq,
      List.append_cancel_right_eq]
    rfl

theorem Action.concatWait_run {q r : Regex α} {s : Pos w} {arg : PartialMatches w}
    (term : ∀ mat ∈ arg, r.Terminates w mat.1 mat.2)
    : (mk [.concatWait q r s] arg).run (concatWait_terminates.mpr term)
      = (arg.pmap (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt) term).flatten := by
  step
  cases arg with | nil => step | cons ent mat =>
    simp only [reduceCtorEq, ↓reduceDIte, List.map_cons, List.pmap_cons,
      List.flatten_cons]
    simp [concat_run term]

theorem matchPartial_concat (q r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/⟨q⟩ ⟨r⟩/].Terminates w s cap)
    : matchPartial [/⟨q⟩ ⟨r⟩/] w s cap term
      = ((q.matchPartial w s cap (concat_terminates.mp term).1).pmap
          (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt)
            (concat_terminates.mp term).2).flatten := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  rw! [← matchPartial_eq_run]
  rw [Action.concatWait_run (concat_terminates.mp term).2]

theorem Action.or_run {s : Pos w} {fst arg : PartialMatches w}
    : (mk [.or s fst] arg).run or_terminates = fst ++ arg := by step; step

theorem Action.orWait_run {r : Regex α} {s : Pos w} {cap : Captures w}
    {arg : PartialMatches w} (term : r.Terminates w s cap)
    : (mk [.orWait r s cap] arg).run (orWait_terminates.mpr term)
      = arg ++ r.matchPartial w s cap term := by step; run_top!; step; step; rfl

theorem matchPartial_or (q r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap)
    : matchPartial [/⟨q⟩ | ⟨r⟩/] w s cap term
      = q.matchPartial w s cap (or_terminates.mp term).1 ++
        r.matchPartial w s cap (or_terminates.mp term).2 := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  rw [Action.orWait_run (or_terminates.mp term).2]
  rfl

theorem Action.filterEmpty_run {emp : Bool} {s : Pos w} {arg : PartialMatches w}
    : (mk [.filterEmpty emp s] arg).run filterEmpty_terminates
      = arg.filter fun ent => (s = ent.1) = emp := by step; step

theorem matchPartial_filterEmpty (emp : Bool) (r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/⟨r⟩ ‹emp›ε/].Terminates w s cap)
    : matchPartial [/⟨r⟩ ‹emp›ε/] w s cap term =
      (r.matchPartial w s cap (filterEmpty_terminates.mp term)).filter
        fun ent ↦ (s = ent.1) = emp := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  simp only [Action.filterEmpty_run, eq_iff_iff, Bool.decide_iff_dist, Bool.decide_eq_true]
  rfl

theorem matchPartial_star_greedy_terminates' {r : Regex α} {s : Pos w}
    {cap : Captures w}
    : [/⟨r⟩*/].Terminates w s cap ↔
      [/(⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*) | ε/].Terminates w s cap := by
  simp only [Terminates, initMatchPartial]; conv_lhs => step

theorem matchPartial_star_lazy_terminates' {r : Regex α} {s : Pos w}
    {cap : Captures w}
    : [/⟨r⟩*?/].Terminates w s cap ↔
      [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*?)/].Terminates w s cap := by
  simp only [Terminates, initMatchPartial]; conv_lhs => step

/-- `star t r` terminates iff `r` terminates and `r` terminates for every
advancing end position and match provided by `r` -/
theorem star_terminates {t : StarType} {r : Regex α} {s : Pos w}
    {cap : Captures w}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ (term : r.Terminates w s cap) ∧
      ∀ mat ∈ r.matchPartial w s cap term,
        s ≠ mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2 := by
  rw [Terminates, initMatchPartial]
  step only [List.append_nil]
  cases t with
  | greedy =>
    simp only
    rw [← matchPartial_terminates_iff, or_terminates,
      or_terminates] at ⊢
    rw! [filterEmpty_terminates, concat_terminates,
      filterEmpty_terminates]
    simp [dand_iff_and_forall, empty_terminates, matchPartial_filterEmpty]
  | lazy =>
    simp only
    rw [← matchPartial_terminates_iff, or_terminates,
      or_terminates] at ⊢
    rw! [filterEmpty_terminates, concat_terminates,
      filterEmpty_terminates]
    simp [dand_iff_and_forall, empty_terminates, matchPartial_filterEmpty]

theorem matchPartial_star (t : StarType) (r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/⟨r⟩*‹t›/].Terminates w s cap)
    : matchPartial [/⟨r⟩*‹t›/] w s cap term = match t with
      | .greedy => [/(⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*) | ε/].matchPartial w s cap
        (matchPartial_star_greedy_terminates'.mp term)
      | .lazy => [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*?)/].matchPartial w s cap
        (matchPartial_star_lazy_terminates'.mp term)
      := by
  simp only [matchPartial_eq_run]
  split <;> conv_lhs => step

theorem matchPartial_start (s : Pos w) (cap : Captures w)
    : matchPartial [/⊢/] w s cap start_terminates
      = if s = 0 then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_end' (s : Pos w) (cap : Captures w)
    : matchPartial [/⊣/] w s cap end'_terminates
      = if s = s.end' then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.capture_run {n : ℕ} {s : Pos w} {arg : PartialMatches w}
    : (mk [.capture n s] arg).run capture_terminates
      = arg.map fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by step; step

theorem matchPartial_capture (n : ℕ) (r : Regex α) (s : Pos w) (cap : Captures w)
    (term : [/(‹n› ⟨r⟩)/].Terminates w s cap)
    : matchPartial [/(‹n› ⟨r⟩)/] w s cap term =
      (r.matchPartial w s cap (capture_terminates.mp term)).map
        fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  simp only [Action.capture_run]
  rfl

/-- `list` always terminates -/
theorem list_terminates {l : List α} {s : Pos w} {cap : Captures w}
    : (list l).Terminates w s cap := by
  induction l generalizing s with
  | nil => rw [list]; exact empty_terminates
  | cons a as ind =>
    rw [list, concat_terminates]
    simp only [matchPartial_unit, List.mem_dite_nil_right, List.mem_cons,
      List.not_mem_nil, or_false, forall_exists_index, forall_eq_apply_imp_iff,
      dand_iff_and_forall, unit_terminates, forall_const, true_and]
    exact fun _ ↦ ind

/-- `backref` always terminates -/
theorem backref_terminates {d : BackrefDefault} {n : ℕ}
    {s : Pos w} {cap : Captures w}
    : [/\‹d›n/].Terminates w s cap := by
  rw [matchPartial_terminates_iff]
  step
  split <;> expose_names
  · split <;> (step; step)
  exact list_terminates

theorem matchPartial_list (l : List α) (s : Pos w) (cap : Captures w)
    : matchPartial (list l) w s cap list_terminates =
    if h : w.extract s.val (s.val + l.length) = l
      then [(s.addOfIndex h rfl, cap)] else [] := by
  induction l generalizing s with
  | nil => simp [list, matchPartial_empty, Icc.addOfIndex]
  | cons a as ind =>
    simp only [list, matchPartial_concat, List.length_cons, matchPartial_unit]
    by_cases! h : w[s.val]? = a
    · specialize ind (s.succOfIndex h)
      simp only [h, ↓reduceDIte, List.pmap_cons, ind, Icc.succOfIndex_val,
        List.pmap_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw! [← add_assoc, add_right_comm]
      have eq : (w.extract (s.val + 1) (s.val + as.length + 1) = as)
          = (w.extract (s.val) (s.val + as.length + 1) = a :: as) := by
        simp only [List.extract_eq_drop_take, Nat.reduceSubDiff, add_tsub_cancel_left,
        eq_iff_iff]
        rw [add_assoc, Nat.add_sub_cancel_left]
        have ⟨lt, wsa⟩ := List.getElem?_eq_some_iff.mp h
        conv_rhs => rw [List.drop_eq_getElem_cons lt, List.take_cons (by linarith), wsa]
        simp
      simp only [eq]
      split
      · simp [← Icc.val_inj, add_assoc, add_comm 1]
      · rfl
    simp only [h, ↓reduceDIte, List.pmap_nil, List.flatten_nil, List.extract_eq_drop_take,
      right_eq_dite_iff, List.ne_cons_self, imp_false]
    by_cases! h' : s.val < w.length
    · contrapose! h
      rw [Nat.add_sub_cancel_left, List.drop_eq_getElem_cons h',
        List.take_cons (by linarith)] at h
      simp only [add_tsub_cancel_right, List.cons.injEq] at h
      rw [← h.1, List.getElem?_eq_some_getElem_iff]; trivial
    · simp [List.drop_eq_nil_of_le h']

theorem matchPartial_backref (d : BackrefDefault) (n : ℕ) (s : Pos w) (cap : Captures w)
    : matchPartial [/\‹d›n/] w s cap backref_terminates =
      match (cap n).head? with
      | none => match d with | .bot => [] | .empty => [(s, cap)]
      | some (cs, ct) => if h : w.extract s.val (s.val + (ct.val - cs.val))
          = w.extract cs.val ct.val
        then [(s.addOfIndex h (List.length_extract_nat' cs.is_le ct.is_le), cap)]
        else [] := by
  rw [matchPartial_eq_run]
  step only [List.append_nil]
  let he := (cap n).head?
  have heeq : he = (cap n).head? := rfl
  cases h : he <;> expose_names -- motive wasn't type correct :(
  · simp only [← heeq, h]
    split <;> (step; step)
  · simp only [← heeq, h]
    rw! [← matchPartial_eq_run, matchPartial_list,
      List.length_extract_nat' val.1.is_le val.2.is_le]
    rfl

end MatchPartial

section Tactic

open Lean Parser Tactic

macro "termination" : tactic =>
  `(tactic| simp [
    bot_terminates, empty_terminates, unit_terminates, concat_terminates,
    or_terminates, filterEmpty_terminates, start_terminates, end'_terminates,
    capture_terminates, backref_terminates])

end Tactic

def match' (r : Regex α) (w : List α) (term : r.Terminates w 0 0) :
  PartialMatches w := [/⟨r⟩ ⊣/].matchPartial w 0 0
    (concat_terminates.mpr ⟨term, fun _ _ ↦ end'_terminates⟩)

#eval match' [/(‹1› 0 | 1) 1 2 3/] [0, 1, 2, 3] (by termination)

--mutual
----def matchPartialStar (t : StarType) (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
----    : List (IccFrom s × Captures w) :=
----  matchPartial r w s cap >>=
----  /- Matching an empty string means you can't continue -/
----    fun (s', cap') ↦ if s.val = s'.val then pure (s', cap') else
----      (fun (s'', cap'') ↦ (s'.widenLeft s'', cap'')) <$>
----      matchPartial (star t r) w s'.expandZero cap'
----termination_by (star t r, s.distToEnd, 0)
----decreasing_by
----  · simp only [Prod.lex_def, star.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_irrefl,
----      Nat.not_lt_zero, and_false, or_self, or_false]
----    exact Nat.lt_add_right (sizeOf t) Nat.zero_lt_one
----  · rename_i hs
----    simp only [Prod.lex_def, star.sizeOf_spec, Nat.lt_irrefl, Nat.not_lt_zero, and_false,
----      or_false, true_and, false_or]
----    apply Icc.distToEnd_lt
----    rcases lt_or_eq_of_le s'.is_ge with slt | seq
----    · exact slt
----    · contradiction
--
--/-- Partial match: takes a regex, a string, a start position, and a list of
--current captures, and returns a list of possible matches to check in order.
--Each match is an end position combined with a capture list. -/
--partial def matchPartial (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
--    : List (IccFrom s × Captures w) :=
--  match r with
--  | bot => failure
--  | empty => pure (s.iccFrom, cap)
--  | unit c => if hs : w[s.val]? = c then pure (Icc.succOfIndex hs, cap) else failure
--  | concat q r => do
--      let (s', cap') ← q.matchPartial w s cap
--      let (s'', cap'') ← r.matchPartial w s'.expandZero cap'
--      pure (s'.widenLeft s'', cap'')
--  | or q r => q.matchPartial w s cap ++ r.matchPartial w s cap
--  | filterEmpty emp r => do
--      let (s', cap') ← r.matchPartial w s cap
--      if (s'.val = s.val) = emp then pure (s', cap') else failure
--  --| star t r => match t with
--  --  | .greedy => matchPartialStar .greedy r w s cap ++ pure (s.iccFrom, cap)
--  --  | .lazy => pure (s.iccFrom, cap) ++ matchPartialStar .lazy r w s cap
--  | star t r => match t with
--    | .greedy => matchPartial [/(¥ᵣ(r) •ε | (¥ᵣ(r) -ε) ¥ᵣ(r)*) | ε/] w s cap
--    | .lazy => matchPartial [/ε | (¥ᵣ(r) •ε | (¥ᵣ(r) -ε) ¥ᵣ(r)*?)/] w s cap
--  | capture n r => do
--      let (s', cap') ← r.matchPartial w s cap
--      pure (s', cap'.update n (pure ⟨s, s'⟩))
--  | backref d n => do
--      let ⟨cs, ct⟩ ← if let some w' := (cap n).getLast? then pure w'
--        else return (← matchPartial d w s cap)
--      if h : w.extract s.val (s.val + (ct.val - cs.val)) = w.extract cs.val ct.val then
--        pure (Icc.addOfIndex h (length_extract_pos_posFrom cs ct), cap) else failure
----termination_by (s.distToEnd, r.numRawStars, r)
----decreasing_by
----  all_goals have sizelt (a b : ℕ) : a < 1 + a + b := by linarith
----  all_goals have zz (n : ℕ) : 0 < n ∨ n = 0 := by omega
----  any_goals simp [Prod.lex_def, numRawStars, sizelt, ← le_iff_lt_or_eq, zz]
--end
--
--theorem matchPartial_bot (w : List α) (s : Pos w) (cap : Captures w)
--    : matchPartial [/⊥/] w s cap = [] := by
--  simp [matchPartial, failure]
--
--theorem matchPartial_empty (w : List α) (s : Pos w) (cap : Captures w)
--    : matchPartial [//] w s cap = [(s.iccFrom, cap)] := by
--  simp [matchPartial]
--
----theorem matchPartial_star_nil (t : StarType) (r : Regex α) (s : Pos []) (cap : Captures [])
----    : Prod.fst <$> (star t r).matchPartial [] s cap =
----      if matchPartial r [] s cap = [] then [s.posFrom] else [s.posFrom, s.posFrom] := by
----  rcases t
----  · simp only [matchPartial, List.pure_def, List.cons_append, List.nil_append,
----      List.map_eq_map, List.map_cons]
----    simp only [matchPartialStar, Prod.mk.eta, List.pure_def, List.map_eq_map,
----      List.bind_eq_flatMap]
----    split_ifs with h
----    · simp [h]
----    ·
--
--/-- A finishing partial match -/
--def matchFinish (r : Regex α) (w : List α) (s : Pos w) (cap : Captures w)
--    : Option (Captures w) :=
--  Prod.snd <$> (matchPartial r w s cap).find? fun (s, _) ↦ s = s.end'
--
--/-- Matches a regex against an entire string.
--Returns a list of captures if it succeeds.
--Called `match'` because `match` is a keyword. -/
--def match' (r : Regex α) (w : List α) : Option (Captures w) := matchFinish r w 0 0
--  --Prod.snd <$> (matchPartial r w 0 0).find? fun (s, _) ↦ s = Pos.end'
--
--theorem match'_bot (w : List α) : match' [/⊥/] w = none := by
--  simp [match', matchFinish, matchPartial_bot]
--
--theorem match'_empty (w : List α) : match' [//] w = if w = [] then some 0 else none := by
--  simp only [match', matchFinish, matchPartial_empty, List.find?_singleton,
--    decide_eq_true_eq, Option.map_eq_map, Option.map_if]
--  congr
--  rw [Icc.zero_end']
--  rfl
--
--theorem match'_unit (c : α) (w : List α)
--    : match' [/c/] w = if w = [c] then some 0 else none := by
--  simp only [match', matchFinish, matchPartial, List.pure_def, Option.map_eq_map]
--  split_ifs with w0c wc wc
--  · simp only [List.find?_singleton, decide_eq_true_eq, Option.map_if,
--      ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not]
--    rw [← Subtype.val_inj]
--    simp [Icc.succOfIndex, wc]
--  · simp only [List.find?_singleton, decide_eq_true_eq, Option.map_if, ite_eq_right_iff,
--      reduceCtorEq, imp_false]
--    contrapose! wc
--    apply_fun Subtype.val at wc
--    simp only [Icc.zero_val, Icc.succOfIndex_val, zero_add, Icc.end'_val] at wc
--    rw [Icc.zero_val] at w0c
--    rw [eq_comm, List.length_eq_one_iff] at wc
--    rcases wc with ⟨a, wa⟩
--    have wa' := congrArg (·[0]?) wa
--    simp only [w0c, List.length_cons, List.length_nil, zero_add, zero_lt_one,
--      getElem?_pos, List.getElem_cons_zero, Option.some.injEq] at wa'
--    exact wa' ▸ wa
--  · simp [wc] at w0c
--  · simp [failure]
--
--theorem match'_concat (q r : Regex α) (w : List α)
--    : match' [/¥ᵣ(q)¥ᵣ(r)/] w = (matchPartial q w 0 0).findSome?
--        (fun (s, cap) ↦ matchFinish r w s cap) := by
--  simp only [match', matchFinish, matchPartial, List.pure_def, List.bind_eq_flatMap,
--    List.find?_flatMap, List.find?_singleton, decide_eq_true_eq, Option.map_eq_map,
--    List.map_findSome?]
--  congr
--  rw [Function.comp_def]
--  ext x cs
--  rw [Option.map_eq_some_iff, Option.map_eq_some_iff]
--  simp only [Prod.exists, exists_eq_right]
--  simp only [List.findSome?_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
--    Prod.mk.injEq, ite_eq_right_iff, reduceCtorEq, imp_false, Prod.forall,
--    exists_and_right, Prod.exists, ↓existsAndEq, and_true]
--  rw [exists_comm]
--  apply exists_congr; intro s
--  simp only [List.find?_eq_some_iff_append, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
--    Bool.not_true, decide_eq_false_iff_not, Prod.forall, exists_and_right,
--    ← Icc.val_inj]
--  rw [← exists_and_left]
--  apply exists_congr; intro csl
--  rw [and_left_comm]
--  rfl
--
--theorem match'_or (q r : Regex α) (w : List α)
--    : match' (or q r) w = (match' q w <|> match' r w) := by
--  simp only [match', matchFinish, matchPartial, List.find?_append, Option.map_eq_map,
--    Option.orElse_eq_orElse, Option.orElse_eq_or]
--  rw [Option.map_or]
--
--/-- Matching specialized to strings. -/
--def matchStr (r : Regex Char) (w : String) := match' r w.toList
--
--def isMatch (r : Regex α) (w : List α) := ∃ cs, match' r w = some cs
--
--theorem isMatch_bot (w : List α) : ¬isMatch [/⊥/] w := by
--  simp [isMatch, match'_bot]
--
--theorem isMatch_empty (w : List α) : isMatch [//] w ↔ w = [] := by
--  simp [isMatch, match'_empty]
--
--theorem isMatch_unit (c : α) (w : List α) : isMatch [/c/] w ↔ w = [c] := by
--  simp [isMatch, match'_unit]
--
--theorem isMatch_or (q r : Regex α) (w : List α)
--    : isMatch (or q r) w ↔ isMatch q w ∨ isMatch r w := by
--  simp only [isMatch, match'_or, Option.orElse_eq_orElse, Option.orElse_eq_or,
--    Option.or_eq_some_iff]
--  constructor <;> intro excs
--  · rcases excs with ⟨cs, qcs | ⟨q0, rcs⟩⟩
--    · exact Or.inl ⟨cs, qcs⟩
--    · exact Or.inr ⟨cs, rcs⟩
--  · by_cases qcs : ∃ cs, q.match' w = some cs
--    · rcases qcs with ⟨cs, qcs⟩
--      exact ⟨cs, Or.inl qcs⟩
--    · simp only [qcs, false_or] at excs
--      push_neg at qcs
--      rw [← Option.eq_none_iff_forall_ne_some] at qcs
--      rcases excs with ⟨cs, rcs⟩
--      exact ⟨cs, Or.inr ⟨qcs, rcs⟩⟩
--
--def language (r : Regex α) : Language α := {w | isMatch r w}
--
--theorem language_bot (α : Type*) [DecidableEq α] : ([/⊥/] : Regex α).language = 0 := by
--  simp [language, isMatch_bot]
--  rfl
--
--theorem language_empty (α : Type*) [DecidableEq α] : ([//] : Regex α).language = {[]} := by
--  simp [language, isMatch_empty]
--
--theorem language_unit (c : α) : [/c/].language = {[c]} := by
--  simp [language, isMatch_unit]
--
--theorem language_or (q r : Regex α) : (or q r).language = q.language + r.language := by
--  simp [language, isMatch_or, Language.add_def, Set.union_def]
--
--#eval matchStr [/(1 ← ('0' | '1')*) \⊥1/] "011011"

end Regex
