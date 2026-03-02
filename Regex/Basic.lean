import Mathlib.Data.List.Monad
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Tactic
import Regex.Algorithm.Termination
import Regex.List

namespace Regex

--def decreasingStrongRec {n : ℕ} {motive : (m : ℕ) → m ≤ n → Sort u}
--    (ind : ∀ m, (mn : m ≤ n) →
--      (∀ k, (kn : k ≤ n) → (km : k > m) → motive k kn) →
--      motive m mn)
--    (m : ℕ) (mn : m ≤ n)
--    : motive m mn :=
--  ind m mn fun k kn _ ↦ decreasingStrongRec ind k kn

variable {ℓ : ℕ} {α : Type*} [deq : DecidableEq α] {r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w}

theorem StarType.map_match {α β : Type*} (f : α → β) (t : StarType) (g l : α)
    : f (match t with | .greedy => g | .lazy => l) =
      match t with | .greedy => f g | .lazy => f l := by rcases t <;> simp

theorem StarType.flatten_match {α : Type*} (t : StarType) (gg gl lg ll : α)
    : (match t with
        | .greedy => match t with | .greedy => gg | .lazy => gl
        | .lazy => match t with | .greedy => lg | .lazy => ll) =
      (match t with | .greedy => gg | .lazy => ll) := by rcases t <;> simp

/-- Initialize a partial match stack -/
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

theorem matchPartial_terminates_iff
    : r.Terminates w s cap ↔ (mk [.regex r s cap] []).Terminates := iff_of_eq rfl

theorem matchPartial_eq_run
  {term : r.Terminates w s cap}
    : r.matchPartial w s cap term = (mk [.regex r s cap] []).run term := rfl

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
    {old new arg : PartialMatches w}
    : (MatchStack.mk [concat r old new] arg).Terminates ↔
      ∀ mat ∈ old, r.Terminates w mat.1 mat.2 := by
  constructor
  · intro term mat mem
    induction old generalizing new arg with | nil => contradiction | cons ent mat' ind =>
      step at term
      run_top! at term with term' term
      rw [List.mem_cons] at mem
      rcases mem with mem | mem
      · exact mem ▸ term'
      · exact ind term mem
  · intro term
    induction old generalizing new arg with | nil => step; step | cons ent mat' ind =>
      step
      run_top!
      use term ent List.mem_cons_self
      exact ind fun m mem ↦ term _ (List.mem_cons_of_mem _ mem)

theorem Action.terminates_concatWait {r : Regex α} {arg : PartialMatches w}
    : (MatchStack.mk [concatWait r] arg).Terminates ↔
      ∀ mat ∈ arg, r.Terminates w mat.1 mat.2 := by
  step only [List.append_nil]
  exact terminates_concat

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

theorem Action.terminates_or {fst arg : PartialMatches w}
    : (MatchStack.mk [or (w := w) fst] arg).Terminates := by step; step

theorem Action.terminates_orWait
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

theorem Action.terminates_star {t : StarType}
    {old new arg : PartialMatches w}
    : (MatchStack.mk [star t r s cap old new] arg).Terminates ↔
      ∀ mat ∈ old, s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2 := by
  constructor
  · intro term mat mem slt
    induction old generalizing cap new arg with | nil => contradiction | cons ent mat' ind =>
      step at term
      rw [List.mem_cons] at mem
      split at term <;> rename_i hs
      · run_top! at term with term' term
        rcases mem with mem | mem
        · exact mem ▸ term'
        · exact ind term mem
      · rcases mem with mem | mem
        · exact (hs (mem ▸ slt)).elim
        · exact ind term mem
  · intro term
    induction old generalizing cap new arg with | nil => step; step | cons ent mat' ind =>
      step
      split <;> rename_i hs
      · run_top!
        use term ent List.mem_cons_self hs
        exact ind fun m mem ↦ term _ (List.mem_cons_of_mem _ mem)
      · exact ind fun m mem ↦ term _ (List.mem_cons_of_mem _ mem)

theorem Action.terminates_starWait {t : StarType} {arg : PartialMatches w}
    : (MatchStack.mk [starWait t r s cap] arg).Terminates ↔
      ∀ mat ∈ arg, s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2 := by
  step only [List.append_nil]
  exact terminates_star

/-- `star t r` terminates iff `r` terminates and `r` terminates for every
advancing end position and match provided by `r` -/
theorem terminates_star {t : StarType}
    : [/⟨r⟩*‹t›/].Terminates w s cap ↔ ∃ term : r.Terminates w s cap,
      ∀ mat ∈ r.matchPartial w s cap term,
        s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2 := by
  constructor
  · intro term
    rw [Terminates, initMatchPartial] at term
    step at term
    run_top! at term with term' term
    use term'
    intro mat qmat
    rw [matchPartial] at qmat
    rw [Action.terminates_starWait] at term
    exact term mat qmat
  · rintro ⟨qterm, term⟩
    rw [Terminates, initMatchPartial] at ⊢
    step
    run_top! using qterm
    rw [Action.terminates_starWait]
    exact fun mat run ↦ term mat run

/-- `start` always terminates -/
theorem terminates_start
    : [/⊢/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

/-- `end'` always terminates -/
theorem terminates_end'
    : [/⊣/].Terminates w s cap := by rw [Terminates, initMatchPartial]; step; step

theorem Action.terminates_capture {n : ℕ} {arg : PartialMatches w}
    : (MatchStack.mk [capture (α := α) n s] arg).Terminates := by step; step

/-- `capture emp r` terminates iff `r` terminates -/
theorem terminates_capture {n : ℕ}
    : [/(n ← ⟨r⟩)/].Terminates w s cap ↔ r.Terminates w s cap := by
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
      = if h : w[s.val]? = some c then [(s.succOfIndex h, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.concat_run {old new arg : PartialMatches w}
    (term : ∀ mat ∈ old, r.Terminates w mat.1 mat.2)
    : (mk [.concat r old new] arg).run (terminates_concat.mpr term)
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

theorem Action.concatWait_run {r : Regex α} {arg : PartialMatches w}
    (term : ∀ mat ∈ arg, r.Terminates w mat.1 mat.2)
    : (mk [.concatWait r] arg).run (terminates_concatWait.mpr term)
      = (arg.pmap (fun ent rt ↦ r.matchPartial w ent.1 ent.2 rt) term).flatten := by
  step only [List.append_nil]
  exact concat_run term

theorem matchPartial_concat {q r : Regex α}
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

theorem Action.or_run {fst arg : PartialMatches w}
    : (mk [.or (α := α) fst] arg).run terminates_or = fst ++ arg := by step; step

theorem Action.orWait_run {r : Regex α} {s : Pos w} {cap : Captures w}
    {arg : PartialMatches w} (term : r.Terminates w s cap)
    : (mk [.orWait r s cap] arg).run (terminates_orWait.mpr term)
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

theorem Action.star_run {t : StarType} {old new arg : PartialMatches w}
    (term : ∀ mat ∈ old, s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2)
    : (mk [.star t r s cap old new] arg).run (terminates_star.mpr term)
      = let res := new ++ arg ++ (old.pmap (fun ent rt ↦ if h : s < ent.1
          then [/⟨r⟩*‹t›/].matchPartial w ent.1 ent.2 (rt h)
          else [ent]) term).flatten;
        match (generalizing := false) t with
        | .greedy => res ++ [(s, cap)]
        | .lazy => [(s, cap)] ++ res := by
  induction old generalizing new arg with
  | nil => step; step; rfl
  | cons ent mat ind =>
    simp only [List.mem_cons, forall_eq_or_imp, List.pmap_cons,
      List.flatten_cons] at term ⊢
    simp only at ind
    step
    split <;> rename_i hs
    · run_top!
      rw [ind term.2]
      simp; rfl
    · rw [ind term.2]
      simp

theorem Action.starWait_run {t : StarType} {arg : PartialMatches w}
    (term : ∀ mat ∈ arg, s < mat.1 → [/⟨r⟩*‹t›/].Terminates w mat.1 mat.2)
    : (mk [.starWait t r s cap] arg).run (terminates_starWait.mpr term)
      = let res := (arg.pmap (fun ent rt ↦ if h : s < ent.1
          then [/⟨r⟩*‹t›/].matchPartial w ent.1 ent.2 (rt h)
          else [ent]) term).flatten;
        match (generalizing := false) t with
        | .greedy => res ++ [(s, cap)]
        | .lazy => [(s, cap)] ++ res := by
  step only [List.append_nil]
  exact star_run term

theorem matchPartial_star {t : StarType}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap)
    : matchPartial [/⟨r⟩*‹t›/] w s cap term =
      let res := ((r.matchPartial w s cap (terminates_star.mp term).1).pmap
        (fun ent rt ↦ if h : s < ent.1
          then [/⟨r⟩*‹t›/].matchPartial w ent.1 ent.2 (rt h)
          else [ent]) (terminates_star.mp term).2).flatten;
      match (generalizing := false) t with
      | .greedy => res ++ [(s, cap)]
      | .lazy => [(s, cap)] ++ res := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  rw! [← matchPartial_eq_run]
  rw [Action.starWait_run (terminates_star.mp term).2]
  rfl

theorem matchPartial_start
    : matchPartial [/⊢/] w s cap terminates_start
      = if s = 0 then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem matchPartial_end'
    : matchPartial [/⊣/] w s cap terminates_end'
      = if s = w.length then [(s, cap)] else [] := by
  simp only [matchPartial_eq_run]; step; step

theorem Action.capture_run {n : ℕ} {arg : PartialMatches w}
    : (mk [.capture (α := α) n s] arg).run terminates_capture
      = arg.map fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by step; step

theorem matchPartial_capture {n : ℕ}
    (term : [/(n ← ⟨r⟩)/].Terminates w s cap)
    : matchPartial [/(n ← ⟨r⟩)/] w s cap term =
      (r.matchPartial w s cap (terminates_capture.mp term)).map
        fun ent ↦ (ent.1, ent.2.update n [(s, ent.1)]) := by
  rw [matchPartial]
  simp only [initMatchPartial]
  step
  run_top!
  simp only [Action.capture_run]
  rfl

/-- `list` always terminates -/
theorem terminates_list {l : List α}
    : (list l).Terminates w s cap := by
  induction l generalizing s with
  | nil => rw [list]; exact terminates_empty
  | cons a as ind =>
    rw [list, terminates_concat]
    simp only [matchPartial_unit, List.mem_dite_nil_right, List.mem_cons,
      List.not_mem_nil, or_false, forall_exists_index, forall_eq_apply_imp_iff, terminates_unit,
      exists_const]
    exact fun _ ↦ ind

/-- `backref` always terminates -/
theorem terminates_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].Terminates w s cap := by
  rw [matchPartial_terminates_iff]
  step
  split <;> expose_names
  · split <;> (step; step)
  exact terminates_list

theorem matchPartial_list {l : List α}
    : matchPartial (list l) w s cap terminates_list =
    if h : w.extract s (s + l.length) = l then [(s.addOfIndex h rfl, cap)] else [] := by
  induction l generalizing s with
  | nil => simp [← Fin.val_inj, list, matchPartial_empty]
  | cons a as ind =>
    simp only [list, matchPartial_concat, List.length_cons, matchPartial_unit]
    by_cases! h : w[s.val]? = a
    · specialize ind (s := s.succOfIndex h)
      --simp only [Pos.val_succOfIndex] at ind
      rw! [Pos.val_succOfIndex] at ind
      simp only at ind
      simp only [h, ↓reduceDIte, List.pmap_cons, ind,
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
      rw! (castMode := .all) [eq]
      split <;> simp [← Fin.val_inj, add_assoc, add_comm 1]
    simp only [h, ↓reduceDIte, List.pmap_nil, List.flatten_nil, List.extract_eq_drop_take,
      add_tsub_cancel_left, right_eq_dite_iff, List.ne_cons_self, imp_false]
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
      | some (cs, ct) => if h : w.extract s (s + (ct - cs)) = w.extract cs ct
        then [(s.addOfIndex h (List.length_extract_pos _ _), cap)]
        else [] := by
  rw [matchPartial_eq_run]
  step only [List.append_nil]
  let he := (cap n).head?
  have heeq : he = (cap n).head? := rfl
  cases h : he <;> expose_names -- motive wasn't type correct :(
  · simp only [← heeq, h]
    split <;> (step; step)
  · simp only [← heeq, h]
    rw! [← matchPartial_eq_run, matchPartial_list, List.length_extract_pos]
    rfl

end MatchPartial

--/-- A proof of termination can be extracted from a matchPartial -/
--def mem_matchPartial_terminates {r : Regex α} {w} {s} {cap} {term} {mat}
--    (_ : mat ∈ r.matchPartial w s cap term) : r.Terminates w s cap := term

end Regex
