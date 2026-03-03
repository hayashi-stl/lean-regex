import Regex.Basic
import Regex.Termination
import Regex.Lemmas.Mem
import Regex.Match

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {q r : Regex α} {w : List α}
  {s : Pos w} {cap : Captures w}

/-- Whether two regexes are terminates-equivalent.
If two regexes are weakly matchPartial-equivalent, you can replace a
termination predicate in one regex with the other. -/
def TerminatesEquiv (q r : Regex α) :=
  ∀ w s cap, q.Terminates w s cap ↔ r.Terminates w s cap

@[inherit_doc]
scoped notation:25 q:25 " ≃ᵗᵉ " r:26 => TerminatesEquiv q r

namespace TerminatesEquiv

@[refl] theorem refl (r : Regex α) : r ≃ᵗᵉ r := by simp [TerminatesEquiv]

@[symm] theorem symm {q r : Regex α} (qr : q ≃ᵗᵉ r) : r ≃ᵗᵉ q := by
  simp [TerminatesEquiv] at qr ⊢; simp [qr]

@[trans] theorem trans {p q r : Regex α} (pq : p ≃ᵗᵉ q) (qr : q ≃ᵗᵉ r)
    : p ≃ᵗᵉ r := by
  simp [TerminatesEquiv] at pq qr ⊢; simp [pq, qr]

theorem allTerminates (heq : q ≃ᵗᵉ r) : q.AllTerminates ↔ r.AllTerminates := by
  rw [TerminatesEquiv] at heq
  simp only [AllTerminates]
  grind

end TerminatesEquiv

theorem terminatesEquiv_bot_concat {r : Regex α} : [/⊥ ⟨r⟩/] ≃ᵗᵉ [/⊥/] := by
  simp [TerminatesEquiv, terminates_concat, matchPartial_bot]

theorem terminatesEquiv_concat_bot {r : Regex α} (hr : r.AllTerminates)
    : [/⟨r⟩ ⊥/] ≃ᵗᵉ [/⊥/] := by
  simp only [TerminatesEquiv, terminates_concat, terminates_bot, implies_true, exists_prop,
      and_true, iff_true]
  exact hr

theorem terminatesEquiv_empty_concat {r : Regex α} : [/ε ⟨r⟩/] ≃ᵗᵉ r := by
  simp [TerminatesEquiv, terminates_concat, terminates_empty, matchPartial_empty]

theorem terminatesEquiv_concat_empty {r : Regex α} : [/⟨r⟩ ε/] ≃ᵗᵉ r := by
  simp [TerminatesEquiv, terminates_concat, terminates_empty]

theorem terminatesEquiv_concat_assoc {p q r : Regex α}
  : [/(⟨p⟩ ⟨q⟩) ⟨r⟩/] ≃ᵗᵉ [/⟨p⟩ (⟨q⟩ ⟨r⟩)/] := by
  simp only [TerminatesEquiv, terminates_concat, matchPartial_concat, List.mem_flatten,
    List.mem_pmap, ↓existsAndEq, true_and, forall_exists_index]
  intro w s cap
  constructor
  · rintro ⟨⟨pt, pqt⟩, pqrt⟩; grind
  · rintro ⟨pt, fn⟩
    refine ⟨⟨pt, fun mat pm ↦ (fn _ pm).choose⟩, fun mat' mat pm qm ↦ ?_⟩
    have ⟨qt, qrt⟩ := fn _ pm
    exact qrt _ qm

theorem terminatesEquiv_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/] ≃ᵗᵉ [/⟨r⟩ | ⟨q⟩/] := by
  simp [TerminatesEquiv, terminates_or, and_comm]

theorem terminatesEquiv_bot_or {r : Regex α} : [/⊥ | ⟨r⟩/] ≃ᵗᵉ r := by
  simp [TerminatesEquiv, terminates_or, terminates_bot]

theorem terminatesEquiv_or_bot {r : Regex α} : [/⟨r⟩ | ⊥/] ≃ᵗᵉ r := by
  simp [TerminatesEquiv, terminates_or, terminates_bot]

theorem terminatesEquiv_or_concat {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) ⟨r⟩/] ≃ᵗᵉ [/⟨p⟩ ⟨r⟩ | ⟨q⟩ ⟨r⟩/] := by
  simp only [TerminatesEquiv, terminates_concat, matchPartial_or, List.mem_append, Prod.forall,
    terminates_or]
  grind

theorem terminatesEquiv_concat_or {p q r : Regex α}
    : [/⟨p⟩ (⟨q⟩ | ⟨r⟩)/] ≃ᵗᵉ [/⟨p⟩ ⟨q⟩ | ⟨p⟩ ⟨r⟩/] := by
  simp only [TerminatesEquiv, terminates_concat, Prod.forall, terminates_or]
  grind

theorem terminatesEquiv_or_assoc {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) | ⟨r⟩/] ≃ᵗᵉ [/⟨p⟩ | (⟨q⟩ | ⟨r⟩)/] := by
  simp only [TerminatesEquiv, terminates_or]; grind

theorem terminatesEquiv_star_bot : ([/⊥*/] : Regex α) ≃ᵗᵉ [//] := by
  rw [TerminatesEquiv]
  conv in _ ↔ _ => rw [terminates_star]
  simp [terminates_bot, terminates_empty, matchPartial_bot]

theorem terminatesEquiv_star_empty : ([/ε*/] : Regex α) ≃ᵗᵉ [//] := by
  rw [TerminatesEquiv]
  conv in _ ↔ _ => rw [terminates_star]
  simp [terminates_empty, matchPartial_empty]

theorem terminatesEquiv_start_concat {r : Regex α}
    (hr : ∀ w s cap, s ≠ 0 → r.Terminates w s cap) : [/⊢ ⟨r⟩/] ≃ᵗᵉ r := by
  simpa [TerminatesEquiv, terminates_concat, terminates_start, matchPartial_start,
    or_iff_not_imp_left]

theorem terminatesEquiv_concat_end' {r : Regex α} : [/⟨r⟩ ⊣/] ≃ᵗᵉ r := by
  simp [TerminatesEquiv, terminates_concat, terminates_end']

/-- The right side of a `concat` can be replaced with an equivalent regex -/
theorem terminatesEquiv_any_concat {p q r : Regex α} (hqr : q ≃ᵗᵉ r)
  : [/⟨p⟩ ⟨q⟩/] ≃ᵗᵉ [/⟨p⟩ ⟨r⟩/] := by
  simp only [TerminatesEquiv, terminates_concat, Prod.forall]
  conv => enter [2, 2, 2, 1, 1, h, 2, 2]; rw [hqr]
  simp

/-- Whether two regexes are (weakly) matchPartial-equivalent.
If two regexes are weakly matchPartial-equivalent, you can replace
membership predicates of `matchPartial` in one regex with the other. -/
def MatchPartialEquiv (q r : Regex α) := ∃ teq : q ≃ᵗᵉ r,
  ∀ w s cap term mat,
    mat ∈ q.matchPartial w s cap term ↔
    mat ∈ r.matchPartial w s cap ((teq w s cap).mp term)

@[inherit_doc]
scoped notation:25 q:25 " ≃ʷᵖ " r:26 => MatchPartialEquiv q r

namespace MatchPartialEquiv

theorem terminatesEquiv (heq : q ≃ʷᵖ r) : q ≃ᵗᵉ r := heq.1

@[refl] theorem refl (r : Regex α) : r ≃ʷᵖ r := by simp [MatchPartialEquiv, TerminatesEquiv]

@[symm] theorem symm {q r : Regex α} (qr : q ≃ʷᵖ r) : r ≃ʷᵖ q := by
  refine ⟨qr.1.symm, ?_⟩; simp [qr.2]

@[trans] theorem trans {p q r : Regex α} (pq : p ≃ʷᵖ q) (qr : q ≃ʷᵖ r)
    : p ≃ʷᵖ r := by
  refine ⟨pq.1.trans qr.1, ?_⟩; simp [pq.2, qr.2]

end MatchPartialEquiv

theorem matchPartialEquiv_bot_concat {r : Regex α} : [/⊥ ⟨r⟩/] ≃ʷᵖ [/⊥/] := by
  refine ⟨terminatesEquiv_bot_concat, ?_⟩
  simp [matchPartial_concat, matchPartial_bot]

theorem matchPartialEquiv_concat_bot {r : Regex α} (hr : r.AllTerminates)
    : [/⟨r⟩ ⊥/] ≃ʷᵖ [/⊥/] := by
  refine ⟨terminatesEquiv_concat_bot hr, ?_⟩
  simp [matchPartial_concat, matchPartial_bot]

theorem matchPartialEquiv_empty_concat {r : Regex α} : [/ε ⟨r⟩/] ≃ʷᵖ r := by
  refine ⟨terminatesEquiv_empty_concat, ?_⟩
  simp [matchPartial_concat, matchPartial_empty]

theorem matchPartialEquiv_concat_empty {r : Regex α} : [/⟨r⟩ ε/] ≃ʷᵖ r := by
  refine ⟨terminatesEquiv_concat_empty, ?_⟩
  simp [matchPartial_concat, matchPartial_empty]

theorem matchPartialEquiv_concat_assoc {p q r : Regex α}
    : [/(⟨p⟩ ⟨q⟩) ⟨r⟩/] ≃ʷᵖ [/⟨p⟩ (⟨q⟩ ⟨r⟩)/] := by
  refine ⟨terminatesEquiv_concat_assoc, ?_⟩
  simp only [mem_matchPartial_concat]
  intro w s cap term mat
  constructor
  · rintro ⟨mip, ⟨miq, pm, qm⟩, rm⟩; grind
  · rintro ⟨mip, pm, miq, qm, rm⟩
    exact ⟨_, ⟨_, pm, qm⟩, rm⟩

theorem matchPartialEquiv_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/] ≃ʷᵖ [/⟨r⟩ | ⟨q⟩/] := by
  refine ⟨terminatesEquiv_or_comm, ?_⟩
  simp [mem_matchPartial_or, or_comm]

theorem matchPartialEquiv_bot_or {r : Regex α} : [/⊥ | ⟨r⟩/] ≃ʷᵖ r := by
  refine ⟨terminatesEquiv_bot_or, ?_⟩
  simp [matchPartial_or, matchPartial_bot]

theorem matchPartialEquiv_or_bot {r : Regex α} : [/⟨r⟩ | ⊥/] ≃ʷᵖ r :=
  matchPartialEquiv_or_comm.trans matchPartialEquiv_bot_or

theorem matchPartialEquiv_or_concat {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) ⟨r⟩/] ≃ʷᵖ [/⟨p⟩ ⟨r⟩ | ⟨q⟩ ⟨r⟩/] := by
  refine ⟨terminatesEquiv_or_concat, ?_⟩
  simp [mem_matchPartial_or, mem_matchPartial_concat]
  grind

theorem matchPartialEquiv_concat_or {p q r : Regex α}
    : [/⟨p⟩ (⟨q⟩ | ⟨r⟩)/] ≃ʷᵖ [/⟨p⟩ ⟨q⟩ | ⟨p⟩ ⟨r⟩/] := by
  refine ⟨terminatesEquiv_concat_or, ?_⟩
  simp [mem_matchPartial_or, mem_matchPartial_concat]
  grind

theorem matchPartialEquiv_or_assoc {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) | ⟨r⟩/] ≃ʷᵖ [/⟨p⟩ | (⟨q⟩ | ⟨r⟩)/] := by
  refine ⟨terminatesEquiv_or_assoc, ?_⟩; simp [mem_matchPartial_or]; grind

theorem matchPartialEquiv_star_bot : ([/⊥*/] : Regex α) ≃ʷᵖ [//] := by
  refine ⟨terminatesEquiv_star_bot, ?_⟩
  conv in _ ↔ _ => rw [mem_matchPartial_star]
  simp [mem_matchPartial_bot, mem_matchPartial_empty]

theorem matchPartialEquiv_star_empty : ([/ε*/] : Regex α) ≃ʷᵖ [//] := by
  refine ⟨terminatesEquiv_star_empty, ?_⟩
  conv in _ ↔ _ => rw [mem_matchPartial_star]
  simp [mem_matchPartial_empty]

/-- Whether two regexes have the same language
If two regexes have the same language, you can replace
`isMatch`/`language` of one regex with the other. -/
def LanguageEquiv (q r : Regex α) := ∃ teq : q ≃ᵗᵉ r,
  ∀ w term, q.IsMatch w term ↔ r.IsMatch w ((teq w 0 0).mp term)

@[inherit_doc]
scoped notation:25 q:25 " ≃ˡᵃ " r:26 => LanguageEquiv q r

namespace LanguageEquiv

theorem terminatesEquiv (heq : q ≃ˡᵃ r) : q ≃ᵗᵉ r := heq.1

@[refl] theorem refl (r : Regex α) : r ≃ˡᵃ r := by simp [LanguageEquiv, TerminatesEquiv]

@[symm] theorem symm {q r : Regex α} (qr : q ≃ˡᵃ r) : r ≃ˡᵃ q := by
  refine ⟨qr.1.symm, ?_⟩; simp [qr.2]

@[trans] theorem trans {p q r : Regex α} (pq : p ≃ˡᵃ q) (qr : q ≃ˡᵃ r)
    : p ≃ˡᵃ r := by
  refine ⟨pq.1.trans qr.1, ?_⟩; simp [pq.2, qr.2]

theorem language (heq : q ≃ˡᵃ r) (term : ∀ w, q.Terminates w 0 0)
    : q.language term = r.language fun w ↦ (heq.1 w 0 0).mp (term w) := by
  ext w
  simp only [Regex.language]
  exact heq.2 w (term w)

end LanguageEquiv

theorem MatchPartialEquiv.languageEquiv (heq : q ≃ʷᵖ r) : q ≃ˡᵃ r := by
  have ⟨teq, heq⟩ := heq
  use teq
  simp only [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff, decide_eq_true_eq,
    not_forall, Decidable.not_not]
  grind


theorem languageEquiv_bot_concat {r : Regex α} : [/⊥ ⟨r⟩/] ≃ˡᵃ [/⊥/] :=
  matchPartialEquiv_bot_concat.languageEquiv

theorem languageEquiv_concat_bot {r : Regex α} (hr : r.AllTerminates)
    : [/⟨r⟩ ⊥/] ≃ˡᵃ [/⊥/] :=
  (matchPartialEquiv_concat_bot hr).languageEquiv

theorem languageEquiv_empty_concat {r : Regex α} : [/ε ⟨r⟩/] ≃ˡᵃ r :=
  matchPartialEquiv_empty_concat.languageEquiv

theorem languageEquiv_concat_empty {r : Regex α} : [/⟨r⟩ ε/] ≃ˡᵃ r :=
  matchPartialEquiv_concat_empty.languageEquiv

theorem languageEquiv_concat_assoc {p q r : Regex α}
    : [/(⟨p⟩ ⟨q⟩) ⟨r⟩/] ≃ˡᵃ [/⟨p⟩ (⟨q⟩ ⟨r⟩)/] :=
  matchPartialEquiv_concat_assoc.languageEquiv

theorem languageEquiv_or_comm {q r : Regex α}
    : [/⟨q⟩ | ⟨r⟩/] ≃ˡᵃ [/⟨r⟩ | ⟨q⟩/] :=
  matchPartialEquiv_or_comm.languageEquiv

theorem languageEquiv_bot_or {r : Regex α} : [/⊥ | ⟨r⟩/] ≃ˡᵃ r :=
  matchPartialEquiv_bot_or.languageEquiv

theorem languageEquiv_or_bot {r : Regex α} : [/⟨r⟩ | ⊥/] ≃ˡᵃ r :=
  matchPartialEquiv_or_bot.languageEquiv

theorem languageEquiv_or_concat {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) ⟨r⟩/] ≃ˡᵃ [/⟨p⟩ ⟨r⟩ | ⟨q⟩ ⟨r⟩/] :=
  matchPartialEquiv_or_concat.languageEquiv

theorem languageEquiv_concat_or {p q r : Regex α}
    : [/⟨p⟩ (⟨q⟩ | ⟨r⟩)/] ≃ˡᵃ [/⟨p⟩ ⟨q⟩ | ⟨p⟩ ⟨r⟩/] :=
  matchPartialEquiv_concat_or.languageEquiv

theorem languageEquiv_or_assoc {p q r : Regex α}
    : [/(⟨p⟩ | ⟨q⟩) | ⟨r⟩/] ≃ˡᵃ [/⟨p⟩ | (⟨q⟩ | ⟨r⟩)/] :=
  matchPartialEquiv_or_assoc.languageEquiv

theorem languageEquiv_star_bot : ([/⊥*/] : Regex α) ≃ˡᵃ [//] :=
  matchPartialEquiv_star_bot.languageEquiv

theorem languageEquiv_star_empty : ([/ε*/] : Regex α) ≃ˡᵃ [//] :=
  matchPartialEquiv_star_empty.languageEquiv

theorem languageEquiv_start_concat {r : Regex α}
    (hr : ∀ w s cap, s ≠ 0 → r.Terminates w s cap) : [/⊢ ⟨r⟩/] ≃ˡᵃ r := by
  refine ⟨terminatesEquiv_start_concat hr, ?_⟩
  simp [isMatch_concat, matchPartial_start]
  simp [IsMatch, match'_def]

theorem languageEquiv_concat_end' {r : Regex α} : [/⟨r⟩ ⊣/] ≃ˡᵃ r := by
  refine ⟨terminatesEquiv_concat_end', ?_⟩
  simp [isMatch_concat, matchPartial_end']
  simp [IsMatch, match'_def]

theorem languageEquiv_end'_concat {q r : Regex α} (hqr : q ≃ˡᵃ r)
  : [/⊣ ⟨q⟩/] ≃ˡᵃ [/⊣ ⟨r⟩/] := by
  refine ⟨terminatesEquiv_any_concat hqr.1, ?_⟩
  simp only [isMatch_concat, Prod.exists, exists_and_right, matchPartial_end', Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, List.mem_ite_nil_right, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  intro w term
  constructor <;> (
    rintro ⟨s, cap, ⟨len0, s0, cap0⟩, s', ⟨cap', mem⟩, s'eq⟩
    rw! [s0, cap0] at mem
    generalize_proofs _ term' at mem
    have ism : IsMatch _ w term' := by
      simp only [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff, decide_eq_true_eq,
        Prod.forall, not_forall, Decidable.not_not]
      exact ⟨_, _, mem, s'eq⟩
    first | rw [hqr.2] at ism | rw [hqr.symm.2] at ism
    simp only [IsMatch, match'_def, ne_eq, List.filter_eq_nil_iff, decide_eq_true_eq,
      Prod.forall, not_forall, Decidable.not_not] at ism
    rcases ism with ⟨s', cap', mem, s'eq⟩
    rw! [← s0, ← cap0] at mem
    exact ⟨_, _, ⟨len0, s0, cap0⟩, _, ⟨_, mem⟩, s'eq⟩
  )

/-- Whether two regexes are strongly matchPartial-equivalent.
If two regexes are strongly matchPartial-equivalent, you can replace
*a sub-regex with the other regex* in
membership predicate of `matchPartial` -/
def MatchPartialStrongEquiv (q r : Regex α) := ∃ teq : q ≃ᵗᵉ r,
  ∀ w s cap term,
    (q.matchPartial w s cap term).reverse.dedup.reverse =
    (r.matchPartial w s cap ((teq w s cap).mp term)).reverse.dedup.reverse

@[inherit_doc]
scoped notation:25 q:25 " ≃ʷᵖ! " r:26 => MatchPartialStrongEquiv q r

theorem MatchPartialStrongEquiv.terminatesEquiv (heq : q ≃ʷᵖ! r) : q ≃ᵗᵉ r := heq.1

theorem MatchPartialStrongEquiv.matchPartialEquiv (heq : q ≃ʷᵖ! r) : q ≃ʷᵖ r := by
  refine ⟨heq.1, ?_⟩
  intro w s cap term mat
  rw [← List.mem_reverse, ← List.mem_dedup, ← List.mem_reverse]
  rw [heq.2]
  rw [List.mem_reverse, List.mem_dedup, List.mem_reverse]

--theorem matchPartialStrongEquiv_or_assoc (p q r : Regex α)
--    : [/(⟨p⟩ | ⟨q⟩) | ⟨r⟩/] ≃ʷᵖ! [/⟨p⟩ | (⟨q⟩ | ⟨r⟩)/] := by
--  constructor; rotate_left 1
--  · refl

end Regex
