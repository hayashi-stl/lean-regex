import Mathlib.Tactic

theorem min_or {α : Type*} [LinearOrder α] (a b : α)
    : min a b = a ∧ min a b ≤ b ∨ min a b = b ∧ min a b ≤ a := by simp [le_total]

--protected theorem Nat.sub_lt_sub_iff_left {a b c : Nat}
--  (h : c ≤ a) : a - c < b - c ↔ a < b := by omega

namespace Regex

variable {α : Type u} [deq : DecidableEq α] {w : List α}

/-- Probably easier to work with than `Fin` and subtyping at the same time.
`Icc a b` is the subtype of natural numbers `n` where `a ≤ n ≤ b`. -/
def Icc (a b : ℕ) := {x : ℕ // a ≤ x ∧ x ≤ b}
  deriving LE, LT, DecidableEq, Repr, Min, Max, LinearOrder,
    Std.LawfulOrderMin, Std.LawfulOrderMax
instance Icc.decLt {a b : ℕ} (i j : Icc a b) : Decidable (LT.lt i j) := Nat.decLt ..
instance Icc.decLe {a b : ℕ} (i j : Icc a b) : Decidable (LE.le i j) := Nat.decLe ..

section Icc

variable {a b : ℕ}

/-- A valid position in a string `w` (including the end) -/
@[reducible] def Pos (w : List α) := Icc 0 w.length deriving Repr
/-- A position from `c` to `b` -/
@[reducible] def IccFrom (c : Icc a b) := Icc c.val b deriving Repr
/-- A position from `a` to `c` -/
@[reducible] def IccTo (c : Icc a b) := Icc a c.val deriving Repr

namespace Icc

theorem val_inj {s t : Icc a b} : s.val = t.val ↔ s = t := Subtype.val_inj
theorem val_le_val {s t : Icc a b} : s ≤ t ↔ s.val ≤ t.val := by simp
theorem val_lt_val {s t : Icc a b} : s < t ↔ s.val < t.val := by simp

theorem is_ge (s : Icc a b) : a ≤ s.val := s.property.left
theorem is_le (s : Icc a b) : s.val ≤ b := s.property.right

end Icc

omit deq in
/-- The length of a list extraction using valid positions `s` and `t ≥ s`
is just `t - s` with no underflow -/
@[simp] theorem _root_.List.length_extract_icc (w : List α) (s : Pos w) (t : IccFrom s)
    : (w.extract s.val t.val).length + s.val = t.val := by
  simp only [List.extract_eq_drop_take, List.length_take, List.length_drop]
  have mints : min (t.val - s.val) (w.length - s.val) = t.val - s.val := by
    rw [min_eq_iff]
    exact Or.inl ⟨rfl, (Nat.sub_le_sub_iff_right s.is_le).mpr t.is_le⟩
  rw [mints, Nat.sub_add_cancel t.is_ge]

omit deq in
/-- The length of a list extraction using valid positions `s` and `t ≥ s`
is just `t - s` with no underflow -/
@[simp] theorem _root_.List.length_extract_nat {w : List α} {s t : ℕ}
    (hs : s ≤ t) (ht : t ≤ w.length)
    : (w.extract s t).length + s = t := by
  let spos : Pos w := ⟨s, ⟨Nat.zero_le _, .trans hs ht⟩⟩
  let tpos : IccFrom spos := ⟨t, ⟨hs, ht⟩⟩
  have lex := List.length_extract_icc w spos tpos
  simp only [spos, tpos] at lex
  exact lex

--@[simp] theorem root_.List.min?_append (as bs : List α) (d : α)
--    : (as ++ bs).min? = as.m

omit deq in
/-- The length of a list extraction using valid positions `s` and `t`
is just `t - s`, potentially with underflow -/
@[simp] theorem _root_.List.length_extract_icc' (w : List α) (s : Pos w) (t : Pos w)
    : (w.extract s.val t.val).length = t.val - s.val := by
  simp only [List.extract_eq_drop_take, List.length_take, List.length_drop,
    inf_eq_left, tsub_le_iff_right]
  rw [Nat.sub_add_cancel s.prop.2]
  exact t.prop.2

omit deq in
/-- The length of a list extraction using valid positions `s` and `t`
is just `t - s`, potentially with underflow -/
@[simp] theorem _root_.List.length_extract_nat' {w : List α} {s t : ℕ}
    (hs : s ≤ w.length) (ht : t ≤ w.length)
    : (w.extract s t).length = t - s :=
  List.length_extract_icc' w ⟨s, ⟨Nat.zero_le _, hs⟩⟩ ⟨t, ⟨Nat.zero_le _, ht⟩⟩

namespace Icc

instance instZero : Zero (Icc 0 b) := ⟨0, ⟨le_refl 0, Nat.zero_le b⟩⟩

@[simp] theorem zero_val : (0 : Icc 0 b).val = 0 := rfl

/-- Turns `s` into a value bounded by itself and `b` -/
def iccFrom (s : Icc a b) : IccFrom s := ⟨s.val, ⟨le_refl s.val, s.is_le⟩⟩

/-- Turns `s` into a value bounded by `a` and itself -/
def iccTo (s : Icc a b) : IccTo s := ⟨s.val, ⟨s.is_ge, le_refl s.val⟩⟩

@[simp] theorem iccFrom_val (s : Icc a b) : s.iccFrom.val = s.val := rfl
@[simp] theorem iccTo_val (s : Icc a b) : s.iccTo.val = s.val := rfl

theorem le_of_mem_iccFrom {s t : Icc a b} {t' : IccFrom s} (ht : t.val = t'.val)
    : s.val ≤ t.val := ht ▸ t'.is_ge

theorem ne_of_lt_of_mem_iccFrom {s t : Icc a b} (t' : IccFrom s) (ht : t.val < s.val)
    : t.val ≠ t'.val := by
  contrapose! ht
  exact le_of_mem_iccFrom ht

/-- Expands the bounds of `s` -/
def expand (s : Icc a b) {a' b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') : Icc a' b' :=
  ⟨s.val, ⟨le_trans ha s.is_ge, le_trans s.is_le hb⟩⟩

/-- Expands the lower bound of `s` -/
def expandLeft (s : Icc a b) {a' : ℕ} (ha : a' ≤ a) : Icc a' b :=
  s.expand ha (le_refl b)

/-- Expands the upper bound of `s` -/
def expandRight (s : Icc a b) {b' : ℕ} (hb : b ≤ b') : Icc a b' :=
  s.expand (le_refl a) hb

/-- Expands the lower bound of `s` to 0 -/
def expandZero (s : Icc a b) : Icc 0 b := s.expandLeft (Nat.zero_le a)

@[simp] theorem expand_val (s : Icc a b) {a' b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b')
    : (s.expand ha hb).val = s.val := by rfl

@[simp] theorem expandZero_val (s : Icc a b)
    : s.expandZero.val = s.val := by rfl

@[simp] theorem expand_eq (s : Icc a b) : s.expand (le_refl a) (le_refl b) = s := rfl

@[simp] theorem iccFrom_expandLeft (s : Icc a b) {a' : ℕ} (ha : a' ≤ a)
    : IccFrom (s.expandLeft ha) = IccFrom s := rfl

@[simp] theorem iccTo_expandRight (s : Icc a b) {b' : ℕ} (hb : b ≤ b')
    : IccTo (s.expandRight hb) = IccTo s := rfl

@[simp] theorem iccFrom_expandZero (s : Icc a b)
    : IccFrom s.expandZero = IccFrom s := rfl

/-- Use `s` to expand the lower bound of `s'` to the lower bound of `s` -/
def widenLeft {s : Icc a b} (s' : IccFrom s) : Icc a b := s'.expandLeft s.is_ge

/-- Use `s` to expand the upper bound of `s'` to the upper bound of `s` -/
def widenRight {s : Icc a b} (s' : IccTo s) : Icc a b := s'.expandRight s.is_le

def widenLeft' {s : Icc a b} (s' : IccFrom s) (a' : IccTo s) : Icc a'.val b :=
  s'.expandLeft a'.is_le

def widenRight' {s : Icc a b} (s' : IccTo s) (b' : IccFrom s) : Icc a b'.val :=
  s'.expandRight b'.is_ge

@[simp] theorem widenLeft_val {s : Icc a b} (s' : IccFrom s)
    : (s.widenLeft s').val = s'.val := rfl

@[simp] theorem widenRight_val {s : Icc a b} (s' : IccTo s)
    : (s.widenRight s').val = s'.val := rfl

@[simp] theorem widenLeft'_val {s : Icc a b} (s' : IccFrom s) (a' : IccTo s)
    : (s.widenLeft' s' a').val = s'.val := rfl

@[simp] theorem widenRight'_val {s : Icc a b} (s' : IccTo s) (b' : IccFrom s)
    : (s.widenRight' s' b').val = s'.val := rfl

/-- Given a subinterval to restrict positions `s` and `t` to, gives an new `s'` and `t'`
for that subinterval -/
def extract (s : Pos w) (t : IccFrom s) (a : IccTo s) (b : IccFrom t)
    : (s' : Pos (w.extract a.val b.val)) × IccFrom s' :=
  ⟨⟨s.val - a.val, ⟨Nat.zero_le (s.val - a.val), by
    simp only [List.extract_eq_drop_take, List.length_take, List.length_drop,
      le_inf_iff, tsub_le_iff_right]
    rw [Nat.sub_add_cancel (le_trans a.is_le (le_trans t.is_ge b.is_ge))]
    rw [Nat.sub_add_cancel (le_trans a.is_le s.is_le)]
    exact ⟨le_trans t.is_ge b.is_ge, s.is_le⟩⟩⟩,
  ⟨t.val - a.val, ⟨by
    simp only [tsub_le_iff_right]
    rw [Nat.sub_add_cancel (le_trans a.is_le t.is_ge)]
    exact t.is_ge,
  by
    simp only [List.extract_eq_drop_take, List.length_take, List.length_drop,
      le_inf_iff, tsub_le_iff_right]
    rw [Nat.sub_add_cancel (le_trans a.is_le (le_trans t.is_ge b.is_ge))]
    rw [Nat.sub_add_cancel (le_trans a.is_le s.is_le)]
    exact ⟨b.is_ge, t.is_le⟩
    ⟩⟩⟩

omit deq in
@[simp] theorem extract_fst_val
    (s : Pos w) (t : IccFrom s) (a : IccTo s) (b : IccFrom t)
    : (s.extract t a b).fst.val = s.val - a.val := rfl

omit deq in
@[simp] theorem extract_snd_val
    (s : Pos w) (t : IccFrom s) (a : IccTo s) (b : IccFrom t)
    : (s.extract t a b).snd.val = t.val - a.val := rfl

omit deq in
theorem extract_fst_eq (s : Pos w) (t t' : IccFrom s) (a : IccTo s) (b : IccFrom t)
    (hb : t'.val ≤ b.val)
    : (s.extract t a b).fst = (s.extract t' a ⟨b.val, ⟨hb, b.is_le⟩⟩).fst := by rfl

/-- Given a subinterval `s, t`, computes the new subinterval `s', t'`
in word `wa ++ w ++ wb` that exactly contains `w` -/
def recycle (s : Pos w) (t : Pos w) (wa wb : List α)
    : Pos (wa ++ w.extract s.val t.val ++ wb) ×
      Pos (wa ++ w.extract s.val t.val ++ wb) :=
  ⟨⟨wa.length, ⟨Nat.zero_le _, by simp⟩⟩,
  ⟨wa.length + (t.val - s.val), ⟨Nat.zero_le _, by
    rw [List.length_append, List.length_append, List.length_extract_icc']
    simp⟩⟩⟩

omit deq in
@[simp] theorem recycle_fst_val {s : Pos w} {t : Pos w} {wa wb : List α}
    : (s.recycle t wa wb).fst.val = wa.length := rfl

omit deq in
@[simp] theorem recycle_snd_val {s : Pos w} {t : Pos w} {wa wb : List α}
    : (s.recycle t wa wb).snd.val = wa.length + (t.val - s.val) := rfl

--theorem extract_eq {s : Pos w} {t t' : IccFrom s} {a a' : IccTo s}
--    {b : IccFrom t} {b' : IccFrom t'}
--    (ht : t.val = t'.val) (ha : a.val = a'.val) (hb : b.val = b'.val)
--    : s.extract t a b = hb ▸ ha ▸ s.extract t' a' b' := by
--  ext
--  simp [← val_inj, eqRec_eq_cast]

/-- The lower bound -/
def start (s : Icc a b) : Icc a b := ⟨a, ⟨le_refl a, le_trans s.is_ge s.is_le⟩⟩

/-- The upper bound -/
def end' (s : Icc a b) : Icc a b := ⟨b, ⟨le_trans s.is_ge s.is_le, le_refl b⟩⟩

@[simp] theorem start_val (s : Icc a b) : s.start.val = a := rfl
@[simp] theorem end'_val (s : Icc a b) : s.end'.val = b := rfl

@[simp] theorem start_eq {s : Icc a b} (t : Icc a b) : s.start = t.start := rfl
@[simp] theorem end'_eq {s : Icc a b} (t : Icc a b) : s.end' = t.end' := rfl

theorem start_le (s t : Icc a b) : t.start ≤ s := s.is_ge
theorem le_end' (s t : Icc a b) : s ≤ t.end' := s.is_le

/-- Distance to the upper bound -/
def distToEnd (s : Icc a b) := s.end'.val - s.val

theorem distToEnd_lt {s t : Icc a b} : s < t ↔ distToEnd t < distToEnd s := by
  have leend := t.is_le
  simp only [distToEnd, val_lt_val, end']
  omega

theorem distToEnd_le {s t : Icc a b} : s ≤ t ↔ distToEnd t ≤ distToEnd s := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact distToEnd_lt

omit deq
theorem zero_end' : w = [] ↔ (0 : Pos w) = (0 : Pos w).end' := by
  rw [← Subtype.val_inj, zero_val, end'_val, (eq_comm : 0 = w.length ↔ _)]
  exact Iff.symm List.length_eq_zero_iff

def strongRecEnd {motive : Icc a b → Sort u}
    (ind : ∀ s, (∀ s', s < s' → motive s') → motive s) (s : Icc a b)
    : motive s :=
  ind s fun t _lt ↦ strongRecEnd ind t
termination_by s.distToEnd
decreasing_by exact distToEnd_lt.mp _lt

--def succOfIndex {s : Pos w} {c : α} (hs : w[s.val]? = c) : IccFrom s :=
--  ⟨s.val + 1, ⟨Nat.le_add_right s.val 1, by
--    rw [List.getElem?_eq_some_iff] at hs
--    rcases hs with ⟨hs, _⟩
--    exact Nat.add_one_le_of_lt hs
--  ⟩⟩

/-- Use the fact that an item exists at `w[s]` to provably add 1 to `s` -/
def succOfIndex {s : Pos w} {c : α} (hs : w[s.val]? = c) : Pos w :=
  ⟨s.val + 1, ⟨Nat.zero_le _, by
    rw [List.getElem?_eq_some_iff] at hs
    rcases hs with ⟨hs, _⟩
    exact Nat.add_one_le_of_lt hs
  ⟩⟩

omit deq in
@[simp] theorem succOfIndex_val {s : Pos w} {c : α} (hs : w[s.val]? = c)
    : (succOfIndex hs).val = s.val + 1 := by rfl

--def addOfIndex {s : Pos w} {t : ℕ} {cs : List α}
--    (ex : w.extract s.val (s.val + t) = cs) (hcs : cs.length = t) : IccFrom s :=
--  ⟨s.val + t, ⟨Nat.le_add_right s.val t, by
--    rw [← ex, List.extract_eq_drop_take, Nat.add_sub_cancel_left] at hcs
--    have tle := hcs ▸ List.length_take_le' t (List.drop s.val w)
--    rw [List.length_drop] at tle
--    exact Nat.add_le_of_le_sub' s.is_le tle
--  ⟩⟩

/-- Use the fact that the subsequence at position `s` with length `t`
actually has length `t` to provably add `t` to `s` -/
def addOfIndex {s : Pos w} {t : ℕ} {cs : List α}
    (ex : w.extract s.val (s.val + t) = cs) (hcs : cs.length = t) : Pos w :=
  ⟨s.val + t, ⟨Nat.zero_le _, by
    rw [← ex, List.extract_eq_drop_take, Nat.add_sub_cancel_left] at hcs
    have tle := hcs ▸ List.length_take_le' t (List.drop s.val w)
    rw [List.length_drop] at tle
    exact Nat.add_le_of_le_sub' s.is_le tle
  ⟩⟩

omit deq in
@[simp] theorem addOfIndex_val {s : Pos w} {t : ℕ} {cs : List α}
    {ex : w.extract s.val (s.val + t) = cs} {hcs : cs.length = t}
    : (addOfIndex ex hcs).val = s.val + t := by rfl

end Icc

--theorem List.getElem?_extract_lt (w : List α) (s : Pos w) (t : IccFrom s)

end Icc

--def Pos (w : List α) := Icc 0 w.length
--  deriving LE, LT, DecidableEq, DecidableLE, DecidableLT, Repr
--
--def PosFrom (s : Pos w) := Icc s.val w.length
--  deriving LE, LT, DecidableEq, DecidableLE, DecidableLT, Repr
--
--variable {s : Pos w} --{s' : PosFrom s}
--
--namespace Pos
--
--omit deq in
--theorem is_le (s : Pos w) : s.val ≤ w.length := s.property.right
--
--omit deq in
--theorem nil_val (s : Pos ([] : List α)) : s.val = 0 := by
--  apply is_le at s
--  simp only [List.length_nil, nonpos_iff_eq_zero] at s
--  exact s
--
--def posFrom (s : Pos w) : PosFrom s := ⟨s.val, ⟨Nat.le_refl s.val, is_le s⟩⟩
--
--omit deq in
--@[simp] theorem posFrom_val (s : Pos w) : s.posFrom.val = s.val := by rfl
--
--def ofLe {s : ℕ} (hs : s ≤ w.length) : Pos w := ⟨s, ⟨Nat.zero_le s, hs⟩⟩
--
--instance instZero : Zero (Pos w) where
--  zero := ofLe (Nat.zero_le w.length)
--
--omit deq in
--theorem nil_eq (s : Pos ([] : List α)) : s = 0 := by
--  rw [← Subtype.val_inj, nil_val, nil_val]
--
--def end' : Pos w := ofLe (le_refl w.length)
--
--omit deq
--@[simp] theorem zero_val (w : List α) : (0 : Pos w).val = 0 := by rfl
--
--omit deq
--@[simp] theorem end'_val (w : List α) : (Pos.end' : Pos w).val = w.length := by
--  simp [end', ofLe]
--
--def end'PosFrom (s : Pos w) : PosFrom s := ⟨(end' : Pos w).val, by
--  rw [end'_val]; exact ⟨s.is_le, le_refl w.length⟩⟩
--
--omit deq
--theorem zero_end' (w : List α) : w = [] ↔ (0 : Pos w) = (end' : Pos w) := by
--  rw [← Subtype.val_inj, zero_val, end'_val, (eq_comm : 0 = w.length ↔ _)]
--  exact Iff.symm List.length_eq_zero_iff
--
--def succOfLt {s : ℕ} (hs : s < w.length) : Pos w :=
--  ⟨s + 1, ⟨Nat.zero_le (s + 1), Nat.add_one_le_of_lt hs⟩⟩
--
--def succOfIndex {c : α} (hs : w[s.val]? = c) : PosFrom s :=
--  ⟨s.val + 1, ⟨Nat.le_add_right s.val 1, by
--    rw [List.getElem?_eq_some_iff] at hs
--    rcases hs with ⟨hs, _⟩
--    exact Nat.add_one_le_of_lt hs
--  ⟩⟩
--
--@[simp] theorem succOfIndex_val {c : α} (hs : w[s.val]? = c)
--    : (succOfIndex hs).val = s.val + 1 := by
--  simp [succOfIndex]
--
--def addOfIndex {t : ℕ} {cs : List α}
--    (ex : w.extract s.val (s.val + t) = cs) (hcs : cs.length = t) : PosFrom s :=
--  ⟨s.val + t, ⟨Nat.le_add_right s.val t, by
--    rw [← ex, List.extract_eq_drop_take, Nat.add_sub_cancel_left] at hcs
--    have tle := hcs ▸ List.length_take_le' t (List.drop s.val w)
--    rw [List.length_drop] at tle
--    exact Nat.add_le_of_le_sub' s.is_le tle
--  ⟩⟩
--
--def distToEnd (s : Pos w) : ℕ := w.length - s.val
--
--omit deq in
--theorem distToEnd_lt {s t : Pos w} (h : s < t) : distToEnd t < distToEnd s := by
--  simp only [distToEnd]
--  apply Nat.sub_lt_sub_left
--  · rcases lt_or_eq_of_le s.is_le with slt | seq
--    · exact slt
--    · have h : s.val < t.val := h
--      rw [seq, lt_iff_not_ge] at h
--      exact (h t.is_le).elim
--  exact h
--
--end Pos
--
--namespace PosFrom
--
--@[coe] def pos (s' : PosFrom s) : Pos w := Pos.ofLe s'.property.right
--instance : CoeOut (PosFrom s) (Pos w) := ⟨pos⟩
--
--omit deq in
--theorem from_zero (w : List α) : PosFrom (0 : Pos w) = Pos w := by
--  simp [PosFrom, Pos, Pos.zero_val]
--
--omit deq in
--theorem from_zero' (s : PosFrom (0 : Pos w)) : s.pos = s := by rfl
--
--omit deq in
--theorem is_ge (s' : PosFrom s) : s.val ≤ s'.val := s'.property.left
--
--omit deq in
--theorem is_le (s' : PosFrom s) : s'.val ≤ w.length := s'.property.right
--
--omit deq in
--@[simp] theorem pos_val (s' : PosFrom s) : s'.pos.val = s'.val := by simp [pos, Pos.ofLe]
--
--def ofGe {s' : Pos w} (hs' : s ≤ s') : PosFrom s := ⟨s'.val, ⟨hs', s'.is_le⟩⟩
--
--def widen (s' : PosFrom s) (s'' : PosFrom s'.pos) : PosFrom s :=
--  ⟨s''.val, ⟨Nat.le_trans s'.is_ge s''.is_ge, s''.pos.is_le⟩⟩
--
--end PosFrom
--
--omit deq in
--@[simp] theorem Pos.pos_posFrom (s : Pos w) : s.posFrom.pos = s := by
--  simp [PosFrom.pos, Pos.ofLe, Pos.posFrom]
--
--omit deq in
--@[simp] theorem Pos.pos_widen (s' : PosFrom s) (s'' : PosFrom s'.pos)
--    : (s'.widen s'').pos = s''.pos := by
--  simp only [PosFrom.widen]
--  rw [← Subtype.val_inj]
--  simp

/-- A *capture* is a stack of substring positions.
Most programming languages treat this as an `option`,
having only 0 or 1 items on it, but .NET is different. -/
def Capture (w : List α) := List (Pos w × Pos w) deriving DecidableEq, Repr

instance Capture.instZero : Zero (Capture w) where
  zero := []

/-- A map from "names" (actually natural numbers) to captures -/
def Captures (w : List α) := ℕ →₀ Capture w deriving Zero, DFunLike

namespace Captures

omit deq in
@[simp] theorem zero_get {w : List α} {n : ℕ} : (0 : Captures w) n = [] := by rfl

/-- Turns this into a list of (index, capture) pairs -/
def toList (cs : Captures w) : List (ℕ × Capture w) :=
  (fun n => (n, cs n)) <$> cs.support.sort

instance instRepr : Repr (Captures w) where
  reprPrec cs := cs.toList.repr

/-- Because `Finsupp.update` is noncomputable even in cases it doesn't need to be -/
def update (cs : Captures w) (n : ℕ) (c : Capture w) : Captures w :=
  Finsupp.mk
    (support := if c = 0 then cs.support \ {n} else cs.support ∪ {n})
    (toFun := Function.update cs.toFun n c)
    (mem_support_toFun := by
      intro n'
      rw [Function.update]
      split_ifs <;> simp only [Finset.mem_sdiff, Finset.union_singleton, Finset.mem_singleton,
        Finset.mem_insert, Finsupp.mem_support_iff, ne_eq, eq_rec_constant]
      · grind
      · rw [show cs.toFun n' = cs n' by congr 1]; grind
      · grind
      · rw [show cs.toFun n' = cs n' by congr 1]; grind
      )

end Captures

omit deq in
theorem length_extract_pos_posFrom (s : Pos w) (s' : IccFrom s)
    : (w.extract s.val s'.val).length = s'.val - s.val := by
  rw [List.extract_eq_drop_take]
  apply List.length_take_of_le
  rw [List.length_drop]
  apply Nat.sub_le_sub_right s'.is_le

/-- A list of partial matches ((pos × captures) pairs) -/
@[reducible] def PartialMatches (w : List α) := List (Pos w × Captures w)
  deriving Repr

end Regex
