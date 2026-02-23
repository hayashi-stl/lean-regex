import Mathlib.Tactic
import Mathlib.Data.Multiset.DershowitzManna

-- Yeah, this lemma (but with multisets) already has a name, but it's a
-- little annoying to use

-- notation because it's fun
scoped[StackDMO] notation:50 a:51 " ≺[" r:min "] " b:51 => r a b

namespace WellFounded

open StackDMO in
/-- The image over an embedding of a well-founded relation preserves accessibility,
where the relation is defined on the target -/
theorem image_acc {α β : Type*} {r : β → β → Prop} {f : α → β} {a : α}
    (acc : Acc (fun x y ↦ f x ≺[r] f y) a) {b : β} (hb : f a = b)
    : Acc (fun x' y' ↦ ∃ x y, f x = x' ∧ f y = y' ∧ x' ≺[r] y') b := by
  induction acc generalizing b with
  | intro y₀ acc yind =>
    apply Acc.intro
    rintro a ⟨x₁, y₁, fx, fy, rxy⟩
    exact yind x₁ (fx ▸ hb ▸ rxy) fx

open StackDMO in
/-- The image over an embedding of a well-founded relation preserves accessibility,
where the relation is defined on the source -/
theorem image_acc' {α β : Type*} {r : α → α → Prop} {f : α → β}
    (inj : Function.Injective f) {a : α}
    (acc : Acc r a) {b : β} (hb : f a = b)
    : Acc (fun x' y' ↦ ∃ x y, f x = x' ∧ f y = y' ∧ x ≺[r] y) b := by
  induction acc generalizing b with
  | intro y₀ acc yind =>
    apply Acc.intro
    rintro a ⟨x₁, y₁, fx, fy, rxy⟩
    rw [← fy, inj.eq_iff] at hb
    exact yind x₁ (hb ▸ rxy) fx

open StackDMO in
/-- The image over an embedding of a well-founded relation is well-founded -/
theorem image {α β : Type*} {r : β → β → Prop} {f : α → β}
    (wf : WellFounded (fun x y ↦ f x ≺[r] f y))
    : WellFounded (fun x' y' ↦ ∃ x y, f x = x' ∧ f y = y' ∧ x' ≺[r] y') := by
  apply WellFounded.intro
  cases wf; rename_i acc
  intro y₀
  apply Acc.intro
  rintro x₀ ⟨x₁, y₁, fx, fy, rxy⟩
  exact image_acc (acc x₁) fx

end WellFounded

namespace StackDMO
variable {α : Type*} {r : α → α → Prop}

def WF (r : α → α → Prop) := {a : α // Acc r a}

namespace WF

instance instLT : LT (WF r) where
  lt := Relation.TransGen (InvImage r Subtype.val)

instance instWellFoundedLT : WellFoundedLT (WF r) where
  wf := WellFounded.transGen Acc.wfRel.wf

instance instPreorder : Preorder (WF r) where
  le ac ac' := ac < ac' ∨ ac = ac'
  le_refl ac := Or.inr rfl
  le_trans a b c := by
    dsimp [(· < ·)]
    intro ab bc
    rcases ab with ab | ab <;> rcases bc with bc | bc
    · exact Or.inl (Relation.TransGen.trans ab bc)
    · exact Or.inl (bc ▸ ab)
    · exact Or.inl (ab ▸ bc)
    · exact Or.inr (ab ▸ bc)
  lt_iff_le_not_ge := by
    intro a b
    have asymm := WellFounded.asymmetric instWellFoundedLT.wf a b
    simp only [not_or]
    constructor
    · intro ab
      have : b ≠ a := by by_contra!; simp only [this] at asymm ab; exact asymm ab ab
      exact ⟨Or.inl ab, asymm ab, this⟩
    · rintro ⟨lteq, nlt, neq⟩
      rw [eq_comm] at neq
      simp only [neq, or_false] at lteq
      exact lteq

instance instWellFoundedRelation
    : WellFoundedRelation (WF r) :=
  WellFoundedLT.toWellFoundedRelation

end WF

-- When you pop an item from the stack, all items you then push must be less than it
def DMO (r : α → α → Prop) (as bs : List α) :=
  ∃ cs as' b, as = as' ++ cs ∧ bs = b :: cs ∧ ∀ a ∈ as', a ≺[r] b

-- More notation. The 's' stands for stack
scoped notation:50 as:51 " ≺ˢ[" r:min "] " bs:51 => DMO r as bs

theorem DMO.invImage_map {β : Type*} (r : β → β → Prop) (f : α → β)
    (as bs : List α)
    : as ≺ˢ[InvImage r f] bs → as.map f ≺ˢ[r] bs.map f := by
  simp_wf
  simp only [DMO]
  rintro ⟨cs, as', b, aseq, bseq, asr⟩
  use (cs.map f), (as'.map f), (f b)
  simp [*] at *; simpa [asr]

theorem DMO.invImage_map_inj {β : Type*} (r : β → β → Prop) (f : α → β)
    (inj : Function.Injective f)
    (as bs : List α)
    : as ≺ˢ[InvImage r f] bs ↔ as.map f ≺ˢ[r] bs.map f := by
  simp_wf
  simp only [DMO]
  constructor
  · rintro ⟨cs, as', b, aseq, bseq, asr⟩
    use (cs.map f), (as'.map f), (f b)
    simp [*] at *; simpa [asr]
  · rintro ⟨cs, as', b, aseq, bseq, asr⟩
    by_cases! emp : ¬Nonempty α
    · rw [not_nonempty_iff] at emp
      have : bs = [] := List.eq_nil_iff_forall_not_mem.mpr (fun b ↦ emp.elim b)
      simp [this] at bseq
    have amem := fun (a : β) (mem : a ∈ as') ↦ List.exists_of_mem_map
      (aseq ▸ List.mem_append.mpr (Or.inl mem))
    have bmem := List.exists_of_mem_map (bseq ▸ List.mem_cons_self)
    apply_fun (List.map (Function.invFun f)) at aseq bseq
    simp only [List.map_map, Function.invFun_comp inj, List.map_id,
      List.map_append, List.map_cons] at aseq bseq
    use (cs.map (Function.invFun f)), (as'.map (Function.invFun f)), (Function.invFun f b)
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and,
      aseq, bseq] at ⊢
    intro a' a'mem
    obtain ⟨ainv, _, fainv⟩ := amem a' a'mem
    obtain ⟨binv, _, fbinv⟩ := bmem
    rw [Function.invFun_eq ⟨ainv, fainv⟩, Function.invFun_eq ⟨binv, fbinv⟩]
    exact asr a' a'mem

theorem DMO.wf (r : α → α → Prop)
    : WellFounded (fun as bs : List (WF r) ↦ as ≺ˢ[InvImage r Subtype.val] bs) := by
  simp only [DMO]
  simp_wf
  apply Subrelation.wf (r := fun as bs : List (WF r) ↦
    Multiset.IsDershowitzMannaLT (Multiset.ofList as) (Multiset.ofList bs)) _
    (InvImage.wf Multiset.ofList Multiset.wellFounded_isDershowitzMannaLT)
  simp only [Subrelation, Multiset.IsDershowitzMannaLT, Multiset.empty_eq_zero,
    forall_exists_index, and_imp]
  intro as bs cs as' aseq b bacc bseq prec
  use Multiset.ofList cs, Multiset.ofList as', Multiset.ofList [⟨b, bacc⟩]
  simp only [Multiset.coe_singleton, ne_eq, Multiset.singleton_ne_zero,
    not_false_eq_true, Multiset.coe_add, Multiset.coe_eq_coe, Multiset.mem_coe,
    Multiset.mem_singleton, exists_eq_left, true_and, aseq, bseq]
  split_ands
  · exact List.perm_append_comm
  · rw [← Multiset.cons_coe, Multiset.add_comm, Multiset.singleton_add]
  · intro a mem
    specialize prec a.val a.prop mem
    simp only [LT.lt]
    apply Relation.TransGen.single
    simp_wf
    exact prec

theorem DMO.wf_raw (r : α → α → Prop)
    : WellFounded
    (fun as bs : List α ↦ as ≺ˢ[r] bs ∧ ∀ b ∈ bs, Acc r b) := by
  have wf := wf r
  simp only [Subtype.val_injective, invImage_map_inj] at wf
  have wf := WellFounded.image wf
  apply Subrelation.wf _ wf
  simp only [Subrelation, List.map_subtype, List.map_id_fun', id_eq, exists_and_left,
    exists_and_right, and_imp]
  intro as bs prec bacc
  have prec' := prec
  obtain ⟨cs, as', b, aseq, bseq, prec⟩ := prec
  have bacc' := bacc
  simp only [bseq, List.mem_cons, forall_eq_or_imp] at bacc'
  have aacc : ∀ a ∈ as, Acc r a := by
    intro a amem
    simp only [aseq, List.mem_append] at amem
    rcases amem with amem | amem
    · exact Acc.inv bacc'.1 (prec a amem)
    · exact bacc'.2 a amem
  split_ands
  · exact ⟨as.attachWith (Acc r ·) aacc, by simp⟩
  · exact ⟨bs.attachWith (Acc r ·) bacc, by simp⟩
  · exact prec'

end StackDMO
