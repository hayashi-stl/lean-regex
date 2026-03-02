import Regex.Basic
import Regex.Lemmas.Mem

namespace Regex
variable {α : Type u} [deq : DecidableEq α] {r : Regex α} {w : List α}

/-! Stuff about full matches -/

/-- Returns all matches that end at the end of the string -/
def match' (r : Regex α) (w : List α) (term : r.Terminates w 0 0) :
  PartialMatches w := [/⟨r⟩ ⊣/].matchPartial w 0 0
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
    : (Fin.last w.length, cap) ∈ r.match' w term ↔
      (Fin.last w.length, cap) ∈ r.matchPartial w 0 0 term := by
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
  rw [eq_comm, Fin.val_zero, List.length_eq_zero_iff]

/-- A unit regex matches only the singleton sequence that has that unit -/
theorem isMatch_unit {c : α} : [/`‹c›/].IsMatch w terminates_unit ↔ w = [c] := by
  simp only [IsMatch, match'_def, matchPartial_unit, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ne_eq,
    List.filter_eq_nil_iff, List.mem_dite_nil_right, List.mem_cons, List.not_mem_nil, or_false,
    decide_eq_true_eq, forall_exists_index, forall_eq_apply_imp_iff, Pos.val_succOfIndex, zero_add,
    Classical.not_imp, Decidable.not_not]
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
        (lt : 0 < mat.1), ∃ mat' ∈ [/⟨r⟩*‹t›/].matchPartial w mat.1 mat.2
          ((terminates_star.mp term).2 _ mem lt),
        mat'.1 = w.length := by
  simp only [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff, decide_eq_true_eq,
    not_forall, Decidable.not_not]
  conv => enter [1, 1, x]; rw [mem_matchPartial_star]
  constructor
  · rintro ⟨mat, zero | ⟨mid, mem, mem'⟩, len⟩
    · rw [List.eq_nil_iff_length_eq_zero]
      simp [← len]; simp [zero]
    · split at mem' <;> expose_names
      · grind
      · simp only [not_lt, Fin.le_zero_iff] at h
        rw [List.eq_nil_iff_length_eq_zero]
        simp [← len, mem']; simp [h]
  · rintro (emp | ⟨mid, mem, lt, mat, mem', len⟩)
    · use (0, 0)
      rw [List.eq_nil_iff_length_eq_zero] at emp
      simp [emp]
    · grind

-- Some silly ones

/-- The start anchor full-matches only the empty sequence -/
theorem isMatch_start : [/⊢/].IsMatch w terminates_start ↔ w = [] := by
  simp only [IsMatch, match'_def, matchPartial_start, ↓reduceIte, ne_eq, List.filter_eq_nil_iff,
    List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, forall_eq, Decidable.not_not]
  rw [eq_comm, Fin.val_zero, List.length_eq_zero_iff]

/-- The end anchor full-matches only the empty sequence -/
theorem isMatch_end' : [/⊣/].IsMatch w terminates_end' ↔ w = [] := by
  simp only [IsMatch, match'_def, matchPartial_end', ne_eq, List.filter_eq_nil_iff,
    List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq, and_imp,
    forall_eq_apply_imp_iff, imp_not_self, Decidable.not_not]
  rw [eq_comm, Fin.val_zero, List.length_eq_zero_iff]

/-- A capture of `r` matches iff `r` matches -/
theorem isMatch_capture {n : ℕ} {r : Regex α} (term : [/(n ← ⟨r⟩)/].Terminates w 0 0)
    : [/(n ← ⟨r⟩)/].IsMatch w term ↔ r.IsMatch w (terminates_capture.mp term) := by
  simp [IsMatch, match'_def, matchPartial_capture]

/-- A full-match on a backref just defaults -/
theorem isMatch_backref {d : BackrefDefault} {n : ℕ}
    : [/\‹d›n/].IsMatch w terminates_backref ↔ match d with
        | .bot => False
        | .empty => w = [] := by
  simp [IsMatch, match'_def, matchPartial_backref]
  split <;> simp [← List.length_eq_zero_iff, eq_comm]

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

/-- Not a simple language description, but this is the language of a star.
Note that it is *not* the star of the individual language. -/
theorem language_star {t : StarType} {r : Regex α}
    (term : ∀ w, [/⟨r⟩*‹t›/].Terminates w 0 0)
    : [/⟨r⟩*‹t›/].language term =
      {[]} ∪ {w | ∃ (mat : _)
        (mem : mat ∈ r.matchPartial w 0 0 (terminates_star.mp (term w)).1)
        (lt : 0 < mat.1), ∃ mat' ∈ [/⟨r⟩*‹t›/].matchPartial w mat.1 mat.2
          ((terminates_star.mp (term w)).2 _ mem lt),
        mat'.1 = w.length} := by
  simp [language, isMatch_star]
  simp [Set.insert_def]

theorem language_start : ([/⊢/] : Regex α).language (fun _ ↦ terminates_start) = {[]} := by
  simp [language, isMatch_start]

theorem language_end' : ([/⊣/] : Regex α).language (fun _ ↦ terminates_end') = {[]} := by
  simp [language, isMatch_end']

theorem language_capture {n : ℕ} {r : Regex α} (term : ∀ w, [/(n ← ⟨r⟩)/].Terminates w 0 0)
    : ([/(n ← ⟨r⟩)/] : Regex α).language term =
      r.language (fun _ ↦ terminates_capture.mp (term _)) := by
  simp [language, isMatch_capture]

theorem language_backref {d : BackrefDefault} {n : ℕ}
    : ([/\‹d›n/] : Regex α).language (fun _ ↦ terminates_backref) = match d with
      | .bot => 0
      | .empty => {[]} := by
  simp [language, isMatch_backref]
  split <;> simp; rfl

end Regex
