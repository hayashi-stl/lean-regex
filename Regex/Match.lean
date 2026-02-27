import Regex.Basic
import Regex.Lemmas.Bounds

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

/-- Convenience theorem for membership of a star match, as suggested by `simp` -/
theorem mem_matchPartial_star {t : StarType} {s} {cap}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap) (mat)
    : mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term ↔
      mat ∈ r.matchPartial w s cap (terminates_star.mp term).1 ∧ mat.1 ≤ s ∨
      (∃ (mid : _) (mem : mid ∈ r.matchPartial w s cap (terminates_star.mp term).1 ∧
        s < mid.1), mat ∈ [/⟨r⟩*/].matchPartial w mid.1 mid.2
          (terminates_star_iff_greedy.mp ((terminates_star.mp term).2 _ mem.1 mem.2))) ∨
      mat = (s, cap) := by
  revert term; rw! [terminates_star_iff_greedy]; intro term
  rw [mem_matchPartial_star_iff_greedy]
  rw [matchPartial_star]
  simp [matchPartial_or, matchPartial_filterEmpty, matchPartial_concat,
    matchPartial_empty]

private theorem mem_matchPartial_star'α {t : StarType} {s} {cap}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap) {mat}
    : mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term →
      ∃ (ls : List (ℕ × Captures)) (nemp : ls ≠ []),
        ls.head nemp = (s, cap) ∧ ls.getLast nemp = mat ∧
        ∀ (i : _) (h : i + 1 < ls.length),
          ∃ term' : r.Terminates w ls[i].1 ls[i].2,
          ls[i + 1] ∈ r.matchPartial w ls[i].1 ls[i].2 term' ∧
          (i + 2 = ls.length ∨ ls[i].1 < ls[i + 1].1) := by
  revert term; rw! [terminates_star_iff_greedy]; intro term
  rw [mem_matchPartial_star_iff_greedy]
  by_cases! sle : s ≤ w.length
  · induction s, sle using decreasingStrongRec generalizing cap mat with | ind s sle ind =>
      rw [mem_matchPartial_star]
      rintro (mem | ⟨mid, mem, mem'⟩ | eq)
      · use [(s, cap), mat]
        simp only [List.head_cons, ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_cons,
          List.getLast_singleton, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
          List.getElem_cons_succ, List.getElem_singleton, true_and, reduceCtorEq, exists_const]
        intro i i0
        simp only [show i = 0 by linarith, List.getElem_cons_zero, zero_add, true_or, and_true]
        exact ⟨(terminates_star.mp term).1, mem.1⟩
      · have ⟨ls', nemp', fst', lst', conn'⟩ :=
          ind _ (endInBounds _ _ sle _ _ _ mem.1) mem.2
          ((terminates_star.mp term).2 _ mem.1 mem.2) mem'
        use (s, cap) :: ls'
        simp only [List.head_cons, List.getLast_cons nemp', lst', List.length_cons,
          Order.lt_add_one_iff, Order.add_one_le_iff, Nat.reduceEqDiff, List.getElem_cons_succ,
          true_and, ne_eq, reduceCtorEq, not_false_eq_true, exists_const]
        intro i ilt
        cases i with
        | zero => simp [List.getElem_zero_eq_head, fst', (terminates_star.mp term).1, mem]
        | succ i =>
          specialize conn' i ilt
          simp only [List.getElem_cons_succ]
          exact conn'
      · use [(s, cap)]; simp [eq]
  · rw [mem_matchPartial_star]
    rintro (mem | ⟨mid, mem, mem'⟩ | eq)
    · use [(s, cap), mat]
      simp only [List.head_cons, ne_eq, List.cons_ne_self, not_false_eq_true, List.getLast_cons,
        List.getLast_singleton, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.add_eq_right, List.getElem_cons_succ, List.getElem_singleton, true_and, reduceCtorEq,
        exists_const]
      intro i i0
      simp only [show i = 0 by linarith, List.getElem_cons_zero, true_or, and_true]
      exact ⟨(terminates_star.mp term).1, mem.1⟩
    · have bound := matchPartial_outOfBounds_eq (le_of_lt sle) mem.1; simp [bound] at mem
    · use [(s, cap)]; simp [eq]

private theorem mem_matchPartial_star'β {t : StarType} {s} {cap}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap) {mat}
    : (∃ (ls : List (ℕ × Captures)) (nemp : ls ≠ []),
        ls.head nemp = (s, cap) ∧ ls.getLast nemp = mat ∧
        ∀ (i : _) (h : i + 1 < ls.length),
          ∃ term' : r.Terminates w ls[i].1 ls[i].2,
          ls[i + 1] ∈ r.matchPartial w ls[i].1 ls[i].2 term' ∧
          (i + 2 = ls.length ∨ ls[i].1 < ls[i + 1].1)) →
      mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term := by
  revert term; rw! [terminates_star_iff_greedy]; intro term
  rw [mem_matchPartial_star_iff_greedy]
  rintro ⟨ls, nemp, fst, lst, conn⟩
  induction ls generalizing s cap mat <;> try contradiction
  rename_i l ls ind
  rw [mem_matchPartial_star]
  cases ls with
  | nil =>
    rw [List.head_singleton] at fst
    simp [fst] at lst
    simp [lst]
  | cons l' ls =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.head_cons, List.length_cons,
      Order.lt_add_one_iff, Order.add_one_le_iff, Nat.reduceEqDiff, List.getElem_cons_succ,
      forall_true_left, Prod.forall, List.getLast_cons, add_le_add_iff_right,
      Nat.add_right_cancel_iff] at ind fst lst conn
    have conn0 := conn 0 (Nat.zero_le _)
    simp only [List.getElem_cons_zero, exists_and_right, fst] at conn0
    have ⟨⟨term', mem⟩, zeq⟩ := conn0
    by_cases! l'le : l'.1 ≤ s
    · simp only [not_lt.mpr l'le, or_false] at zeq
      rw [eq_comm, ← List.eq_nil_iff_length_eq_zero] at zeq
      simp only [zeq, List.getLast_singleton] at lst
      exact Or.inl ⟨lst ▸ mem, lst ▸ l'le⟩
    have term'' := (terminates_star.mp term).2 _ mem l'le
    specialize ind _ _ term'' rfl lst _
    · intro i ilt
      specialize conn (i + 1) (by linarith)
      simp only [List.getElem_cons_succ, exists_and_right] at conn ⊢
      exact conn
    exact Or.inr (Or.inl ⟨_, ⟨mem, l'le⟩, ind⟩)

/-- Non-recursive version of membership of a star match -/
theorem mem_matchPartial_star' {t : StarType} {s} {cap}
    (term : [/⟨r⟩*‹t›/].Terminates w s cap) {mat}
    : mat ∈ [/⟨r⟩*‹t›/].matchPartial w s cap term ↔
      ∃ (ls : List (ℕ × Captures)) (nemp : ls ≠ []),
        ls.head nemp = (s, cap) ∧ ls.getLast nemp = mat ∧
        ∀ (i : _) (h : i + 1 < ls.length),
          ∃ term' : r.Terminates w ls[i].1 ls[i].2,
          ls[i + 1] ∈ r.matchPartial w ls[i].1 ls[i].2 term' ∧
          (i + 2 = ls.length ∨ ls[i].1 < ls[i + 1].1) :=
  ⟨mem_matchPartial_star'α term, mem_matchPartial_star'β term⟩

/-! Stuff about full matches -/

/-- Returns all matches that end at the end of the string -/
def match' (r : Regex α) (w : List α) (term : r.Terminates w 0 0) :
  PartialMatches := [/⟨r⟩ ⊣/].matchPartial w 0 0
    (terminates_concat.mpr ⟨term, fun _ _ ↦ terminates_end'⟩)

theorem match'_def (term : r.Terminates w 0 0)
    : r.match' w term = (r.matchPartial w 0 0 term).filter fun mat ↦ mat.1 = w.length := by
  rw [match', matchPartial_concat]
  simp only [matchPartial_end', Prod.mk.eta, List.pmap_eq_map]
  rw [← List.flatMap_def, ← List.filterMap_eq_filter, List.filterMap_eq_flatMap_toList]
  simp only [Option.guard_apply, decide_eq_true_eq]
  congr; ext mat n mat'
  split <;> simp

theorem mem_match'_iff (term : r.Terminates w 0 0) {mat}
    : mat ∈ r.match' w term ↔
      mat ∈ r.matchPartial w 0 0 term ∧ mat.1 = w.length := by simp [match'_def]

/-- The condition specialized for (w.length, cap) -/
theorem mem_match'_iff_length_mem (term : r.Terminates w 0 0) {cap}
    : (w.length, cap) ∈ r.match' w term ↔
      (w.length, cap) ∈ r.matchPartial w 0 0 term := by
  simp [mem_match'_iff]

/-- Returns whether the whole sequence matches the regex.
We require termination, because weird properties result without that requirement.
(e.g. `q.isMatch w` but not `(or q r).isMatch w` because `r` doesn't terminate) -/
def IsMatch (r : Regex α) (w : List α) (term : r.Terminates w 0 0) :=
  r.match' w term ≠ []

/-- `⊥` never matches -/
theorem isMatch_bot : ¬[/⊥/].IsMatch w terminates_bot := by
  simp [IsMatch, match'_def, matchPartial_bot]

/-- The empty regex matches only the empty string -/
theorem isMatch_empty : [//].IsMatch w terminates_empty ↔ w = [] := by
  simp only [IsMatch, match'_def, matchPartial_empty, ne_eq, List.filter_eq_nil_iff, List.mem_cons,
    List.not_mem_nil, or_false, decide_eq_true_eq, forall_eq, Decidable.not_not]
  rw [eq_comm, List.length_eq_zero_iff]

/-- A unit regex matches only the singleton sequence that has that unit -/
theorem isMatch_unit {c : α} : [/`‹c›/].IsMatch w terminates_unit ↔ w = [c] := by
  simp only [IsMatch, match'_def, matchPartial_unit, zero_add, ne_eq, List.filter_eq_nil_iff,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, and_imp,
    forall_eq_apply_imp_iff, Classical.not_imp, Decidable.not_not]
  rw [eq_comm (a := 1), List.length_eq_one_iff, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨⟨lt, eqc⟩, ⟨c', eqc'⟩⟩
    simp only [eqc', List.getElem_cons_zero, List.cons.injEq, and_true] at eqc ⊢
    exact eqc
  · intro wc; simp [wc]

theorem isMatch_concat {q r : Regex α} (term : [/⟨q⟩ ⟨r⟩/].Terminates w 0 0)
    : [/⟨q⟩ ⟨r⟩/].IsMatch w term ↔
      ∃ mat,
        ∃ (mem : mat ∈ q.matchPartial w 0 0 (terminates_concat.mp term).1),
        ∃ mat' ∈ r.matchPartial w mat.1 mat.2
          ((terminates_concat.mp term).2 _ mem), mat'.1 = w.length := by
  simp [IsMatch, match'_def, matchPartial_concat]

/-- An alternation between `q` and `r` matches iff `q` matches or `r` matches -/
theorem isMatch_or {q r : Regex α} (term : [/⟨q⟩ | ⟨r⟩/].Terminates w 0 0)
    : [/⟨q⟩ | ⟨r⟩/].IsMatch w term ↔
      q.IsMatch w (terminates_or.mp term).1 ∨ r.IsMatch w (terminates_or.mp term).2 := by
  simp [IsMatch, match'_def, matchPartial_or, imp_iff_not_or]

-- Note the intentional use of a greedy star in the recursion.
-- That is an arbitrary choice made for the purpose of uniting the star types.
theorem isMatch_star {t : StarType} {r : Regex α} (term : [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].IsMatch w term ↔
      w = [] ∨
      ∃ (mat : _) (mem : mat ∈ r.matchPartial w 0 0 (terminates_star.mp term).1)
        (lt : 0 < mat.1), ∃ mat' ∈ [/⟨r⟩*/].matchPartial w mat.1 mat.2
          (terminates_star_iff_greedy.mp ((terminates_star.mp term).2 _ mem lt)),
          mat'.1 = w.length := by
  simp only [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff, decide_eq_true_eq, Prod.forall,
    not_forall, Decidable.not_not, exists_and_right, exists_eq_right, Prod.exists]
  simp only [exists_prop, exists_and_right, exists_eq_right]
  conv in _ ∈ _ => rw [mem_matchPartial_star_iff_greedy]
  rw [matchPartial_star]
  simp only [matchPartial_or, matchPartial_filterEmpty, ge_iff_le, nonpos_iff_eq_zero, eq_iff_iff,
    iff_true, matchPartial_concat, Bool.false_eq_true, iff_false, decide_not, matchPartial_empty,
    List.append_assoc, List.mem_append, List.mem_filter, List.length_eq_zero_iff, decide_eq_true_eq,
    List.mem_flatten, List.mem_pmap, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Prod.exists, ↓existsAndEq, true_and, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨cap', mem | ⟨s, cap, mem, mem'⟩ | eq⟩
    · simp [mem]
    · exact Or.inr ⟨_, _, mem.1, Nat.pos_iff_ne_zero.mpr mem.2, _, mem'⟩
    · simp [eq]
  · rintro (eq | ⟨s, cap, mem, lt, cap', mem'⟩)
    · exact ⟨0, Or.inr (Or.inr ⟨eq, rfl⟩)⟩
    · exact ⟨cap', Or.inr (Or.inl ⟨_, _, ⟨mem, Nat.pos_iff_ne_zero.mp lt⟩, mem'⟩)⟩

theorem isMatch_star_greedy_iff_lazy
    {r : Regex α} (term : [/⟨r⟩*/].Terminates w 0 0)
    : [/⟨r⟩*/].IsMatch w term ↔ [/⟨r⟩*?/].IsMatch w
      (terminates_star_greedy_iff_lazy.mp term) := by
  rw [isMatch_star, ← isMatch_star (t := .lazy)];

theorem isMatch_star_iff_greedy {t : StarType}
    {r : Regex α} (term : [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].IsMatch w term ↔ [/⟨r⟩*/].IsMatch w (terminates_star_iff_greedy.mp term) := by
  cases t <;> simp [isMatch_star_greedy_iff_lazy]

theorem isMatch_star_iff_lazy {t : StarType}
    {r : Regex α} (term : [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].IsMatch w term ↔ [/⟨r⟩*?/].IsMatch w (terminates_star_iff_lazy.mp term) := by
  cases t <;> simp [isMatch_star_greedy_iff_lazy]

/-- Non-recursive version, stated with a nonempty list -/
theorem isMatch_star' {t : StarType} {r : Regex α} (term : [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].IsMatch w term ↔
      ∃ (ls : List (ℕ × Captures)) (nemp : ls ≠ []),
        ls.head nemp = (0, 0) ∧ (ls.getLast nemp).1 = w.length ∧
        ∀ (i : _) (h : i + 1 < ls.length),
          ∃ term' : r.Terminates w ls[i].1 ls[i].2,
          ls[i + 1] ∈ r.matchPartial w ls[i].1 ls[i].2 term' ∧
          (i + 2 = ls.length ∨ ls[i].1 < ls[i + 1].1) := by
  rw [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff]
  conv in _ ∈ _ => rw [mem_matchPartial_star']
  push_neg
  conv in (∃ _, _) ∧ _ => rw [← exists_and_right]
  conv in (∃ _, _) ∧ _ => rw [← exists_and_right]
  -- conv stopped working with unknown goal _uniq.321197
  simp only [and_assoc (c := decide _ = _), and_comm (b := decide _ = _)]
  simp

theorem decide_eq_bool {p : Prop} [Decidable p] {b : Bool}
    : decide p = b ↔ (p ↔ b = true) := by cases b <;> simp

theorem isMatch_filterEmpty {e : Bool} {r : Regex α}
    (term : [/⟨r⟩ ‹e›ε/].Terminates w 0 0)
    : [/⟨r⟩ ‹e›ε/].IsMatch w term ↔
      r.IsMatch w (terminates_filterEmpty.mp term) ∧ (w.length = 0) = e := by
  simp [IsMatch, match'_def, matchPartial_filterEmpty, decide_eq_bool]

-- Some silly ones

/-- The start anchor full-matches only the empty sequence -/
theorem isMatch_start : [/⊢/].IsMatch w terminates_start ↔ w = [] := by
  simp only [IsMatch, match'_def, matchPartial_start, ↓reduceIte, ne_eq, List.filter_eq_nil_iff,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, forall_eq, Decidable.not_not]
  rw [eq_comm, List.length_eq_zero_iff]

/-- The end anchor full-matches only the empty sequence -/
theorem isMatch_end' : [/⊣/].IsMatch w terminates_end' ↔ w = [] := by
  simp only [IsMatch, match'_def, matchPartial_end', ne_eq, List.filter_eq_nil_iff,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, and_imp,
    forall_eq_apply_imp_iff, imp_not_self, Decidable.not_not]
  rw [eq_comm, List.length_eq_zero_iff]

/-- A capture of `r` matches iff `r` matches -/
theorem isMatch_capture {n : ℕ} {r : Regex α} (term : [/(‹n› ⟨r⟩)/].Terminates w 0 0)
    : [/(‹n› ⟨r⟩)/].IsMatch w term ↔ r.IsMatch w (terminates_capture.mp term) := by
  simp [IsMatch, match'_def, matchPartial_capture]

/-- A full-match on a backref just defaults -/
theorem isMatch_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].IsMatch w terminates_backref ↔ match d with
        | .bot => False
        | .empty => w = [] := by
  simp [IsMatch, match'_def, matchPartial_backref]
  split <;> simp

/-- The language of a regex is the set of languages that it full-matches. -/
def language (r : Regex α) (term : ∀ w, r.Terminates w 0 0)
  : Language α := {w | IsMatch r w (term w)}

theorem mem_language_iff {r : Regex α} {term : ∀ w, r.Terminates w 0 0} {w}
    : w ∈ r.language term ↔ r.IsMatch w (term w) := by
  simp [language]; rfl

--/-- The reverse direction, because rewriting is being annoying -/
--theorem mem_language_iff' {r : Regex α} {term : ∀ w, r.Terminates w 0 0} {w}
--    : r.IsMatch w (term w) ↔ w ∈ r.language term ↔ r.IsMatch w (term w) := by
--  simp [language]; rfl

theorem language_bot : ([/⊥/] : Regex α).language (fun _ ↦ terminates_bot) = 0 := by
  simp [language, isMatch_bot]; rfl

theorem language_empty : ([//] : Regex α).language (fun _ ↦ terminates_empty) = {[]} := by
  simp [language, isMatch_empty]

theorem language_unit {c : α} : [/c/].language (fun _ ↦ terminates_unit) = {[c]} := by
  simp [language, isMatch_unit]

/-- Not a simple language description, but this is the language of a concat.
Note that it is *not* the concatenation of the individual languages. -/
theorem language_concat {q r : Regex α} (term : ∀ w, [/⟨q⟩ ⟨r⟩/].Terminates w 0 0)
    : [/⟨q⟩ ⟨r⟩/].language term
      = {w | ∃ mat,
        ∃ (mem : mat ∈ q.matchPartial w 0 0 (terminates_concat.mp (term w)).1),
        ∃ mat' ∈ r.matchPartial w mat.1 mat.2
          ((terminates_concat.mp (term w)).2 _ mem), mat'.1 = w.length} := by
  simp [language, isMatch_concat]

theorem language_or {q r : Regex α} (term : ∀ w, [/⟨q⟩ | ⟨r⟩/].Terminates w 0 0)
  : [/⟨q⟩ | ⟨r⟩/].language term
    = q.language (fun _ ↦ (terminates_or.mp (term _)).1) +
      r.language (fun _ ↦ (terminates_or.mp (term _)).2) := by
  simp [language, isMatch_or, Language.add_def, Set.union_def]

theorem language_filterEmpty {e : Bool} {r : Regex α}
    (term : ∀ w, [/⟨r⟩ ‹e›ε/].Terminates w 0 0)
    : ([/⟨r⟩ ‹e›ε/] : Regex α).language term = if e then
        r.language (fun _ ↦ terminates_filterEmpty.mp (term _)) ⊓ {[]} else
        r.language (fun _ ↦ terminates_filterEmpty.mp (term _)) - {[]} := by
  simp only [language, isMatch_filterEmpty, List.length_eq_zero_iff, eq_iff_iff]
  split <;> (expose_names; simp only [h, iff_true, Bool.false_eq_true, iff_false])
  · ext x; rw [Language.mem_inf, Set.setOf_and, Set.mem_inter_iff]; rfl
  · ext x; rw [Language.mem_sub, Set.setOf_and, Set.mem_inter_iff]; rfl

/-- Not a simple language description, but this is the language of a star.
Note that it is *not* the star of the individual language. -/
theorem language_star {t : StarType} {r : Regex α}
    (term : ∀ w, [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].language term =
      {w | ∃ (ls : List (ℕ × Captures)) (nemp : ls ≠ []),
        ls.head nemp = (0, 0) ∧ (ls.getLast nemp).1 = w.length ∧
        ∀ (i : _) (h : i + 1 < ls.length),
          ∃ term' : r.Terminates w ls[i].1 ls[i].2,
          ls[i + 1] ∈ r.matchPartial w ls[i].1 ls[i].2 term' ∧
          (i + 2 = ls.length ∨ ls[i].1 < ls[i + 1].1)} := by
  simp [language, isMatch_star']

theorem language_start : ([/⊢/] : Regex α).language (fun _ ↦ terminates_start) = {[]} := by
  simp [language, isMatch_start]

theorem language_end' : ([/⊣/] : Regex α).language (fun _ ↦ terminates_end') = {[]} := by
  simp [language, isMatch_end']

theorem language_capture {n : ℕ} {r : Regex α} (term : ∀ w, [/(‹n› ⟨r⟩)/].Terminates w 0 0)
    : ([/(‹n› ⟨r⟩)/] : Regex α).language term =
      r.language (fun _ ↦ terminates_capture.mp (term _)) := by
  simp [language, isMatch_capture]

theorem language_backref {d : BackrefDefault} {n : ℕ}
    : ([/\‹d›n/] : Regex α).language (fun _ ↦ terminates_backref) = match d with
      | .bot => 0
      | .empty => {[]} := by
  simp [language, isMatch_backref]
  split <;> simp; rfl

end Regex
