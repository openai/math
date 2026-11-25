import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # Enumerating the singleton slots in a declaration row

At a fixed grouping coordinate and a fixed orientation of the row, a
candidate supplies independent source and destination labels on the other
coordinates. It is a singleton exactly when the reconstructed labels share
a coordinate. Every accepted pair has a consecutive interval of bit offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

variable {n d blocks width : ℕ}

/-- Number of source and destination candidates for one orientation of a row. -/
def singlePairTrials (n d : ℕ) : ℕ := d^n * d^n

/-- The counter first splits into independent numeric labels, each then read
in little-endian base `d`. -/
def singleOtherLabels (n d : ℕ) : Fin (singlePairTrials n d) ≃ Label n d × Label n d :=
  finProdFinEquiv.symm.trans (finFunctionFinEquiv.symm.prodCongr finFunctionFinEquiv.symm)

/-- Source is the quotient by the label count and destination is its remainder. -/
theorem singleOtherLabels_values (t : Fin (singlePairTrials n d)) (j : Fin n) :
    ((singleOtherLabels n d t).1 j).val = t.val / d^n / d^j.val % d ∧
    ((singleOtherLabels n d t).2 j).val = t.val % d^n / d^j.val % d :=
  ⟨rfl, rfl⟩

private def fixedLabel (i : Fin (n+1)) (a : Fin d) :
    Label n d ≃ {x : Label (n+1) d // x i = a} where
  toFun u := ⟨i.insertNth (α := fun _ => Fin d) a u, Fin.insertNth_apply_same (α := fun _ => Fin d) i a u⟩
  invFun x := i.removeNth x.val
  left_inv u := Fin.removeNth_insertNth (α := fun _ => Fin d) i a u
  right_inv x := Subtype.ext ((Fin.insertNth_eq_iff (α := fun _ => Fin d)).mpr ⟨x.property.symm,rfl⟩)

/-- Reconstruct the two whole labels by inserting the specified source and
destination symbols at the grouping coordinate. -/
def singleOrderedPairs (i : Fin (n+1)) (a b : Fin d) : Fin (singlePairTrials n d) ≃
    {x : Label (n+1) d × Label (n+1) d // x.1 i = a ∧ x.2 i = b} :=
  (singleOtherLabels n d).trans (((fixedLabel i a).prodCongr (fixedLabel i b)).trans
    Equiv.subtypeProdEquivProd.symm)

/-- Keep the reconstructed labels if they agree in some coordinate. -/
def singleTrialValid (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d)) : Prop :=
  ¬∀ j, (singleOrderedPairs i a b t).val.1 j ≠ (singleOrderedPairs i a b t).val.2 j

instance (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d)) :
    Decidable (singleTrialValid i a b t) :=
  inferInstanceAs (Decidable (¬∀ j, (singleOrderedPairs i a b t).val.1 j ≠
    (singleOrderedPairs i a b t).val.2 j))

/-- At distinct grouping symbols the shared symbol must be found among the
other coordinates. On a diagonal row every candidate passes this test. -/
theorem singleTrialValid_iff (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d)) :
    singleTrialValid i a b t ↔ a = b ∨
      ∃ j, (singleOtherLabels n d t).1 j = (singleOtherLabels n d t).2 j := by
  change (¬∀ j, i.insertNth (α := fun _ => Fin d) a (singleOtherLabels n d t).1 j ≠
    i.insertNth (α := fun _ => Fin d) b (singleOtherLabels n d t).2 j) ↔ _
  rw [Fin.forall_iff_succAbove i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, not_and_or, not_not,
    not_forall]

/-- The candidates that pass the pair test, each repeated over the available
physical bit offsets in that pair. -/
abbrev SingleScan (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) :=
  {t : Fin (singlePairTrials n d) // singleTrialValid i a b t} × Fin (blocks*width)

/-- Exact enumeration of the singleton slots belonging to one orientation
of the row. The bit index is carried unchanged. -/
def singleOrderedEquiv (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) :
    SingleScan blocks width i a b ≃
      {z : SingleSlot n d blocks width // z.1.val.1 i = a ∧ z.1.val.2 i = b} where
  toFun u :=
    let p := singleOrderedPairs i a b u.1.val
    ⟨(⟨p.val,u.1.property⟩,u.2),p.property⟩
  invFun z :=
    let p := (⟨z.val.1.val,z.property⟩ : {x : Label (n+1) d × Label (n+1) d //
      x.1 i = a ∧ x.2 i = b})
    (⟨(singleOrderedPairs i a b).symm p, by
      unfold singleTrialValid
      rw [Equiv.apply_symm_apply]
      exact z.val.1.property⟩, z.val.2)
  left_inv u := Prod.ext (Subtype.ext ((singleOrderedPairs i a b).symm_apply_apply u.1.val)) rfl
  right_inv z := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

/-- The executable ordered scan emits the accepted singleton at its given offset. -/
def singleTrial (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d))
    (bit : Fin (blocks*width)) : Option (SingleSlot n d blocks width) :=
  if h : singleTrialValid i a b t then some (singleOrderedEquiv blocks width i a b (⟨t,h⟩,bit)).val
  else none

/-- Reading a candidate yields the specified physical bit exactly when both
whole labels and the unchanged bit offset match. -/
theorem singleTrial_some_iff (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d))
    (bit : Fin (blocks*width)) (z : SingleSlot n d blocks width) :
    singleTrial i a b t bit = some z ↔ (singleOrderedPairs i a b t).val = z.1.val ∧ bit = z.2 := by
  unfold singleTrial
  split
  · rw [Option.some.injEq]
    change (⟨_,_⟩,bit) = z ↔ _
    rw [Prod.ext_iff, Subtype.ext_iff]
  · rename_i h
    constructor
    · intro he
      contradiction
    · rintro ⟨he,_⟩
      exact (h (by unfold singleTrialValid; rw [he]; exact z.1.property)).elim

private theorem singleRow_iff (i : Fin (n+1)) (a b : Fin d) (z : SingleSlot n d blocks width) :
    itemRow i (.inr z : Item n d blocks width) = Sym2.mk a b ↔
    (z.1.val.1 i = a ∧ z.1.val.2 i = b) ∨ (z.1.val.1 i = b ∧ z.1.val.2 i = a) :=
  Sym2.eq_iff

/-- An off-diagonal unordered row receives exactly two disjoint ordered
enumerations. The inverse selects the orientation from the source symbol. -/
def singleStrictRowEquiv (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) (hab : a ≠ b) :
    SingleScan blocks width i a b ⊕ SingleScan blocks width i b a ≃
      {z : SingleSlot n d blocks width // itemRow i (.inr z : Item n d blocks width) = Sym2.mk a b} :=
  (Equiv.sumCongr (singleOrderedEquiv blocks width i a b) (singleOrderedEquiv blocks width i b a)).trans
    { toFun := fun
        | .inl z => ⟨z.val,(singleRow_iff i a b z.val).mpr (.inl z.property)⟩
        | .inr z => ⟨z.val,(singleRow_iff i a b z.val).mpr (.inr z.property)⟩
      invFun := fun z => if h : z.val.1.val.1 i = a then
        .inl ⟨z.val, ((singleRow_iff i a b z.val).mp z.property).resolve_right
          (fun h' => hab (h.symm.trans h'.1))⟩
        else .inr ⟨z.val, ((singleRow_iff i a b z.val).mp z.property).resolve_left
          (fun h' => h h'.1)⟩
      left_inv := by
        rintro (z | z)
        · simp only [dite_eq_left z.property.1]
        · have h : z.val.1.val.1 i ≠ a := fun h => hab (h.symm.trans z.property.1)
          simp only [dite_eq_right h]
      right_inv := by
        intro z
        by_cases h : z.val.1.val.1 i = a
        · simp only [dite_eq_left h]
        · simp only [dite_eq_right h] }

/-- On a diagonal row a single ordered scan enumerates each physical singleton
exactly once, with no duplication from swapping two identical symbols. -/
def singleDiagRowEquiv (blocks width : ℕ) (i : Fin (n+1)) (a : Fin d) :
    SingleScan blocks width i a a ≃
      {z : SingleSlot n d blocks width // itemRow i (.inr z : Item n d blocks width) = Sym2.mk a a} :=
  (singleOrderedEquiv blocks width i a a).trans (Equiv.subtypeEquivRight fun z => by
    rw [singleRow_iff, or_self])

private theorem singleScan_card_le (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) :
    Fintype.card (SingleScan blocks width i a b) ≤ singlePairTrials n d * (blocks*width) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_fin] using Fintype.card_subtype_le (singleTrialValid i a b)

/-- For a strict unordered row, two ordered scans suffice, even if every
candidate pair passes. -/
theorem singleStrictRow_card_le (blocks width : ℕ) (i : Fin (n+1)) (a b : Fin d) (hab : a ≠ b) :
    Fintype.card {z : SingleSlot n d blocks width //
      itemRow i (.inr z : Item n d blocks width) = Sym2.mk a b} ≤
        2 * (singlePairTrials n d * (blocks*width)) := by
  rw [← Fintype.card_congr (singleStrictRowEquiv blocks width i a b hab), Fintype.card_sum, two_mul]
  exact Nat.add_le_add (singleScan_card_le blocks width i a b) (singleScan_card_le blocks width i b a)

/-- The diagonal row requires only one ordered scan. -/
theorem singleDiagRow_card_le (blocks width : ℕ) (i : Fin (n+1)) (a : Fin d) :
    Fintype.card {z : SingleSlot n d blocks width //
      itemRow i (.inr z : Item n d blocks width) = Sym2.mk a a} ≤ singlePairTrials n d * (blocks*width) := by
  rw [← Fintype.card_congr (singleDiagRowEquiv blocks width i a)]
  exact singleScan_card_le blocks width i a a

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
