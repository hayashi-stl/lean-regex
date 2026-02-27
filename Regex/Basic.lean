import Mathlib.Data.List.Monad
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Tactic
import Regex.Algorithm.Termination
import Regex.List

namespace Regex

def decreasingStrongRec {n : ℕ} {motive : (m : ℕ) → m ≤ n → Sort u}
    (ind : ∀ m, (mn : m ≤ n) →
      (∀ k, (kn : k ≤ n) → (km : k > m) → motive k kn) →
      motive m mn)
    (m : ℕ) (mn : m ≤ n)
    : motive m mn :=
  ind m mn fun k kn _ ↦ decreasingStrongRec ind k kn

variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : ℕ} {cap : Captures}

theorem StarType.map_match {α β : Type*} (f : α → β) (t : StarType) (g l : α)
    : f (match t with | .greedy => g | .lazy => l) =
      match t with | .greedy => f g | .lazy => f l := by rcases t <;> simp

theorem StarType.flatten_match {α : Type*} (t : StarType) (gg gl lg ll : α)
    : (match t with
        | .greedy => match t with | .greedy => gg | .lazy => gl
        | .lazy => match t with | .greedy => lg | .lazy => ll) =
      (match t with | .greedy => gg | .lazy => ll) := by rcases t <;> simp

/-- Initialize a partial match stack -/
def initMatchPartial (r : Regex α) (w : List α) (s : ℕ) (cap : Captures)
    : MatchStack α where
  entries := [Action.regex r w s cap]
  arg := []

/-- Whether a particular regex match terminates -/
def Terminates (r : Regex α) (w : List α) (s : ℕ) (cap : Captures) :=
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

def matchPartial (r : Regex α) (w : List α) (s : ℕ) (cap : Captures)
  (term : r.Terminates w s cap)
    : PartialMatches := (r.initMatchPartial w s cap).run term

theorem matchPartial_terminates_iff
    : r.Terminates w s cap ↔ (mk [.regex r w s cap] []).Terminates := iff_of_eq rfl

theorem matchPartial_eq_run
  {term : r.Terminates w s cap}
    : r.matchPartial w s cap term = (mk [.regex r w s cap] []).run term := rfl

/-- `bot` always terminates -/
theorem terminates_bot
    : [/⊥/].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

/-- `empty` always terminates -/
theorem terminates_empty
    : [//].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

/-- `unit` always terminates -/
theorem terminates_unit {c : α}
    : [/c/].Terminates w s cap := by
  rw [Terminates, initMatchPartial]; step; step

theorem Action.terminates_concat
    {old new arg : PartialMatches}
    : (MatchStack.mk [concat r w s old new] arg).Terminates ↔
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

theorem Action.terminates_concatWait {q r : Regex α} {arg : PartialMatches}
    : (MatchStack.mk [concatWait q r w s] arg).Terminates ↔
      ∀ mat ∈ arg, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term mat mem
    step at term
    cases arg with | nil => contradiction | cons ent mat' =>
      simp only [reduceCtorEq, ↓reduceDIte, List.map_cons] at term
      rw [terminates_concat] at term
      exact term mat mem
  · intro term
    step
    cases arg with | nil => step | cons ent mat' =>
      simp only [reduceCtorEq, ↓reduceDIte, List.map_cons]
      rwa [terminates_concat]

/-- `concat q r` terminates iff `q` terminates and `r` terminates for every
end position and match provided by `q` -/
theorem terminates_concat {q r : Regex α}
    : [/⟨q⟩ ⟨r⟩/].Terminates w s cap ↔ ∃ term : q.Terminates w s cap,
      ∀ mat ∈ q.matchPartial w s cap term, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term with term' term
    use term'
    intro mat qmat
    rw [matchPartial] at qmat
    rw [Action.terminates_concatWait] at term
    exact term mat qmat
  · rintro ⟨qterm, term⟩
    rw [Terminates, initMatchPartial] at ⊢
    step
    run_top! using qterm
    rw [Action.terminates_concatWait]
    exact fun mat run ↦ term mat run

theorem Action.terminates_or {fst arg : PartialMatches}
    : (MatchStack.mk [or (α := α) s fst] arg).Terminates := by step; step

theorem Action.terminates_orWait
    {arg : PartialMatches}
    : (MatchStack.mk [orWait r w s cap] arg).Terminates ↔ r.Terminates w s cap := by
  constructor
  · intro term
    step at term
    run_top! at term with term' term
    exact term'
  · intro term
    step
    run_top! using term
    exact terminates_or

/-- `or q r` terminates iff `q` terminates and `r` terminates -/
theorem terminates_or {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap ↔
      q.Terminates w s cap ∧ r.Terminates w s cap := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term with term' term
    exact ⟨term', Action.terminates_orWait.mp term⟩
  · rintro ⟨qterm, rterm⟩
    rw [Terminates, initMatchPartial]
    step
    run_top! using qterm
    exact Action.terminates_orWait.mpr rterm

/-- `or` termination is symmetric -/
theorem terminates_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap ↔ [/⟨r⟩ | ⟨q⟩/].Terminates w s cap := by
  simp only [terminates_or]; rw [and_comm]

theorem Action.terminates_filterEmpty {emp : Bool} {arg : PartialMatches}
    : (MatchStack.mk [filterEmpty (α := α) emp s] arg).Terminates := by step; step

/-- `filterEmpty emp r` terminates iff `r` terminates -/
theorem terminates_filterEmpty {emp : Bool}
    : [/⟨r⟩ ‹emp›ε/].Terminates w s cap ↔ r.Terminates w s cap := by
  constructor <;> intro term
  · rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term
    exact term.1
  · rw [Terminates, initMatchPartial]
    step
    run_top!
    exact ⟨term, Action.terminates_filterEmpty⟩

/-- `start` always terminates -/
theorem terminates_start
    : [/⊢/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

/-- `end'` always terminates -/
theorem terminates_end'
    : [/⊣/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

theorem Action.terminates_capture {n : ℕ} {arg : PartialMatches}
    : (MatchStack.mk [capture (α := α) n s] arg).Terminates := by step; step

/-- `capture emp r` terminates iff `r` terminates -/
theorem terminates_capture {n : ℕ}
    : [/(‹n› ⟨r⟩)/].Terminates w s cap ↔ r.Terminates w s cap := by
  constructor <;> intro term
  · rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term
    exact term.1
  · rw [Terminates, initMatchPartial]
    step
    run_top!
    exact ⟨term, Action.terminates_capture⟩

theorem matchPartial_bot
    : matchPartial [/⊥/] w s cap terminates_bot = [] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_empty
    : matchPartial [//] w s cap terminates_empty
    = [(s, cap)] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_unit {c : α}
    : matchPartial [/c/] w s cap terminates_unit
      = if w[s]? = some c then [(s + 1, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.concat_run {old new arg : PartialMatches}
    (term : ∀ mat ∈ old, r.Terminates w mat.1 mat.2)
    : (mk [.concat r w s old new] arg).run (terminates_concat.mpr term)
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

theorem Action.concatWait_run {q r : Regex α} {arg : PartialMatches}
    (term : ∀ mat ∈ arg, r.Terminates w mat.1 mat.2)
    : (mk [.concatWait q r w s] arg).run (terminates_concatWait.mpr term)
      = (arg.pmap (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt) term).flatten := by
  step
  cases arg with | nil => step | cons ent mat =>
    simp only [reduceCtorEq, ↓reduceDIte, List.map_cons, List.pmap_cons,
      List.flatten_cons]
    simp [concat_run term]

theorem matchPartial_concat (q r : Regex α) (s : ℕ) (cap : Captures)
    {term : [/⟨q⟩ ⟨r⟩/].Terminates w s cap}
    : matchPartial [/⟨q⟩ ⟨r⟩/] w s cap term
      = ((q.matchPartial w s cap (terminates_concat.mp term).1).pmap
          (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt)
            (terminates_concat.mp term).2).flatten := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  rw! [← matchPartial_eq_run]
  rw [Action.concatWait_run (terminates_concat.mp term).2]

theorem Action.or_run {s : ℕ} {fst arg : PartialMatches}
    : (mk [.or (α := α) s fst] arg).run terminates_or = fst ++ arg := by step; step

theorem Action.orWait_run {r : Regex α} {s : ℕ} {cap : Captures}
    {arg : PartialMatches} (term : r.Terminates w s cap)
    : (mk [.orWait r w s cap] arg).run (terminates_orWait.mpr term)
      = arg ++ r.matchPartial w s cap term := by step; run_top!; step; step; rfl

theorem matchPartial_or {q r : Regex α}
    {term : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap}
    : matchPartial [/⟨q⟩ | ⟨r⟩/] w s cap term
      = q.matchPartial w s cap (terminates_or.mp term).1 ++
        r.matchPartial w s cap (terminates_or.mp term).2 := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  rw [Action.orWait_run (terminates_or.mp term).2]
  rfl

theorem mem_matchPartial_or_comm {q r : Regex α}
    {term : [/⟨q⟩ | ⟨r⟩/].Terminates w s cap} {mat}
    : mat ∈ matchPartial [/⟨q⟩ | ⟨r⟩/] w s cap term ↔
      mat ∈ matchPartial [/⟨r⟩ | ⟨q⟩/] w s cap (terminates_or_comm.mp term) := by
  simp only [matchPartial_or, List.mem_append]; rw [or_comm]

theorem Action.filterEmpty_run {emp : Bool} {arg : PartialMatches}
    : (mk [.filterEmpty (α := α) emp s] arg).run terminates_filterEmpty
      = arg.filter fun ent => (s ≥ ent.1) = emp := by step; step

theorem matchPartial_filterEmpty (emp : Bool)
    {term : [/⟨r⟩ ‹emp›ε/].Terminates w s cap}
    : matchPartial [/⟨r⟩ ‹emp›ε/] w s cap term =
      (r.matchPartial w s cap (terminates_filterEmpty.mp term)).filter
        fun ent ↦ (s ≥ ent.1) = emp := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  simp only [Action.filterEmpty_run, eq_iff_iff, Bool.decide_iff_dist, Bool.decide_eq_true]
  rfl

theorem matchPartial_star_greedy_terminates'
    : [/⟨r⟩*/].Terminates w s cap ↔
      [/(⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*) | ε/].Terminates w s cap := by
  simp only [Terminates, initMatchPartial]; conv_lhs => step

theorem matchPartial_star_lazy_terminates'
    : [/⟨r⟩*?/].Terminates w s cap ↔
      [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*?)/].Terminates w s cap := by
  simp only [Terminates, initMatchPartial]; conv_lhs => step

theorem terminates_star' {t : StarType}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ match t with
      | .greedy => [/(⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*) | ε/].Terminates w s cap
      | .lazy => [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*?)/].Terminates w s cap := by
  rw [Terminates, initMatchPartial]
  step
  cases t with
  | greedy => simp only [Terminates, initMatchPartial]
  | lazy => simp only [Terminates, initMatchPartial]

/-- `star t r` terminates iff `r` terminates and `r` terminates for every
advancing end position and match provided by `r` -/
theorem terminates_star {t : StarType}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ ∃ term : r.Terminates w s cap,
      ∀ mat ∈ r.matchPartial w s cap term,
        s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2 := by
  rw [Terminates, initMatchPartial]
  step only [List.append_nil]
  cases t with
  | greedy =>
    simp only
    rw [← matchPartial_terminates_iff, terminates_or,
      terminates_or] at ⊢
    rw! [terminates_filterEmpty, terminates_concat,
      terminates_filterEmpty]
    simp [terminates_empty, matchPartial_filterEmpty]
  | lazy =>
    simp only
    rw [← matchPartial_terminates_iff, terminates_or,
      terminates_or] at ⊢
    rw! [terminates_filterEmpty, terminates_concat,
      terminates_filterEmpty]
    simp [terminates_empty, matchPartial_filterEmpty]

theorem matchPartial_star {t : StarType}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap)
    : matchPartial [/⟨r⟩*‹t›/] w s cap term = match t with
      | .greedy => [/(⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*) | ε/].matchPartial w s cap
        (matchPartial_star_greedy_terminates'.mp term)
      | .lazy => [/ε | (⟨r⟩ •ε | (⟨r⟩ -ε) ⟨r⟩*?)/].matchPartial w s cap
        (matchPartial_star_lazy_terminates'.mp term)
      := by
  simp only [matchPartial_eq_run]
  split <;> conv_lhs => step

theorem matchPartial_start
    : matchPartial [/⊢/] w s cap terminates_start
      = if s = 0 then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_end'
    : matchPartial [/⊣/] w s cap terminates_end'
      = if s = w.length then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.capture_run {n : ℕ} {arg : PartialMatches}
    : (mk [.capture (α := α) n s] arg).run terminates_capture
      = arg.map fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by step; step

theorem matchPartial_capture {n : ℕ}
    (term : [/(‹n› ⟨r⟩)/].Terminates w s cap)
    : matchPartial [/(‹n› ⟨r⟩)/] w s cap term =
      (r.matchPartial w s cap (terminates_capture.mp term)).map
        fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  simp only [Action.capture_run]
  rfl

/-- `list` always terminates -/
theorem list_terminates {l : List α}
    : (list l).Terminates w s cap := by
  induction l generalizing s with
  | nil => rw [list]; exact terminates_empty
  | cons a as ind =>
    rw [list, terminates_concat]
    simp only [matchPartial_unit, List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false,
      and_imp, forall_eq_apply_imp_iff, terminates_unit, exists_const]
    exact fun _ ↦ ind

/-- `backref` always terminates -/
theorem terminates_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].Terminates w s cap := by
  rw [matchPartial_terminates_iff]
  step
  split <;> expose_names
  · split <;> (step; step)
  exact list_terminates

theorem matchPartial_list {l : List α}
    : matchPartial (list l) w s cap list_terminates =
    if w.extract s (s + l.length) = l then [(s + l.length, cap)] else [] := by
  induction l generalizing s with
  | nil => simp [list, matchPartial_empty]
  | cons a as ind =>
    simp only [list, matchPartial_concat, List.length_cons, matchPartial_unit]
    by_cases! h : w[s]? = a
    · specialize ind (s := s + 1)
      simp only [h, ↓reduceIte, List.pmap_cons, ind,
        List.pmap_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      rw! [← add_assoc, add_right_comm]
      have eq : (w.extract (s + 1) (s + as.length + 1) = as)
          = (w.extract (s) (s + as.length + 1) = a :: as) := by
        simp only [List.extract_eq_drop_take, Nat.reduceSubDiff, add_tsub_cancel_left,
          eq_iff_iff]
        rw [add_assoc, Nat.add_sub_cancel_left]
        have ⟨lt, wsa⟩ := List.getElem?_eq_some_iff.mp h
        conv_rhs => rw [List.drop_eq_getElem_cons lt, List.take_cons (by linarith), wsa]
        simp
      simp only [eq]
    simp only [h, ↓reduceIte, List.pmap_nil, List.flatten_nil, List.extract_eq_drop_take,
      add_tsub_cancel_left, right_eq_ite_iff, List.ne_cons_self, imp_false]
    by_cases! h' : s < w.length
    · contrapose! h
      rw [List.drop_eq_getElem_cons h', List.take_cons (by linarith)] at h
      simp only [add_tsub_cancel_right, List.cons.injEq] at h
      rw [← h.1, List.getElem?_eq_some_getElem_iff]; trivial
    · simp [List.drop_eq_nil_of_le h']

theorem matchPartial_backref {n : ℕ} {d : BackrefDefault}
    : matchPartial [/\‹d›n/] w s cap terminates_backref =
      match (cap n).head? with
      | none => match d with | .bot => [] | .empty => [(s, cap)]
      | some (cs, ct) => if w.extract s (s + (w.extract cs ct).length) = w.extract cs ct
        then [(s + (w.extract cs ct).length, cap)]
        else [] := by
  rw [matchPartial_eq_run]
  step only [List.append_nil]
  let he := (cap n).head?
  have heeq : he = (cap n).head? := rfl
  cases h : he <;> expose_names -- motive wasn't type correct :(
  · simp only [← heeq, h]
    split <;> (step; step)
  · simp only [← heeq, h]
    rw! [← matchPartial_eq_run, matchPartial_list]
    rfl

end MatchPartial

--/-- A proof of termination can be extracted from a matchPartial -/
--def mem_matchPartial_terminates {r : Regex α} {w} {s} {cap} {term} {mat}
--    (_ : mat ∈ r.matchPartial w s cap term) : r.Terminates w s cap := term

end Regex
