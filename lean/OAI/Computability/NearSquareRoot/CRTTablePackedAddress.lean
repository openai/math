import OAI.Computability.NearSquareRoot.CRTTableAxes
import OAI.Computability.NearSquareRoot.CRTTableWordEquiv
import OAI.Computability.NearSquareRoot.CRTControlledBenesParallel
import OAI.Computability.NearSquareRoot.CRTTableMerge

/-! # The complete CRT address as external coordinates and target word fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

/-- Numeric rank of a padded axis is residue first, followed by padding. -/
def axisNumber {m L : ℕ} [NeZero m] (h : m ≤ L) : ZMod m ⊕ Fin (L-m) ≃ Fin L :=
  let valid : ZMod m ≃ Fin m := {
    toFun := fun x => ⟨x.val,ZMod.val_lt x⟩
    invFun := fun x => x.val
    left_inv := fun x => ZMod.natCast_zmod_val _
    right_inv := fun x => Fin.ext (by simp [ZMod.val_natCast,Nat.mod_eq_of_lt x.isLt]) }
  ((valid.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (Nat.add_sub_of_le h))

theorem axisNumber_val {m L : ℕ} [NeZero m] (h : m ≤ L) (z : ZMod m ⊕ Fin (L-m)) :
    (axisNumber h z).val = coordinate id z := by
  cases z <;> rfl

private noncomputable def fieldOrder (d n : ℕ) : ExternalAxis d n ⊕ TargetIndex d n ≃ Fin d :=
  Equiv.ofBijective (Sum.elim Subtype.val (targetAxis d n)) (by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext h)
        | inr y => exact (x.property ⟨y,h.symm⟩).elim
      | inr x =>
        cases y with
        | inl y => exact (y.property ⟨x,h⟩).elim
        | inr y => exact congrArg Sum.inr (targetAxis_injective d n h)
    · intro g
      by_cases h : g ∈ Set.range (targetAxis d n)
      · obtain ⟨b,rfl⟩ := h
        exact ⟨Sum.inr b,rfl⟩
      · exact ⟨Sum.inl ⟨g,h⟩,rfl⟩)

abbrev AxisValue {d : ℕ} (a w : Fin d → ℕ) (g : Fin d) :=
  ZMod (a g) ⊕ Fin (2^w g-a g)

abbrev ExternalValues {d : ℕ} (a w : Fin d → ℕ) (n : ℕ) :=
  (g : ExternalAxis d n) → AxisValue a w g.val

abbrev Packed {d : ℕ} (a w : Fin d → ℕ) (n : ℕ) :=
  Benes.PackedAddress (ExternalValues a w n) (fun b : TargetIndex d n => w (targetAxis d n b))

variable {d : ℕ} (a w : Fin d → ℕ) [∀ j, NeZero (a j)] (hwidth : ∀ j, a j ≤ 2^w j)

/-- Split a full padded address into its external coordinates and exactly one
fixed-width MSF target word for each (node, right-child position). -/
noncomputable def packAddress (n : ℕ) : ((g : Fin d) → AxisValue a w g) ≃ Packed a w n :=
  let order := fieldOrder d n
  (((Equiv.piCongrLeft (AxisValue a w) order).symm.trans
    (Equiv.sumPiEquivProdPi (fun v => AxisValue a w (order v)))).trans
      ((Equiv.refl (ExternalValues a w n)).prodCongr
        (Equiv.piCongrRight fun b : TargetIndex d n =>
          (axisNumber (hwidth (targetAxis d n b))).trans (wordEquiv (w (targetAxis d n b))))))

theorem packAddress_external (n : ℕ) (y : (g : Fin d) → AxisValue a w g)
    (g : ExternalAxis d n) : (packAddress a w hwidth n y).1 g = y g.val := rfl

theorem packAddress_target (n : ℕ) (y : (g : Fin d) → AxisValue a w g)
    (b : TargetIndex d n) :
    let g := targetAxis d n b
    (packAddress a w hwidth n y).2 b = wordEquiv (w g) (axisNumber (hwidth g) (y g)) := rfl

end CRTTable

end NearSquareRoot
end Computability
end OAI
