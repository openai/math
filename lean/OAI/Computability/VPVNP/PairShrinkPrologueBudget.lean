import OAI.Computability.VPVNP.PairShrinkChildDemandBudget
import OAI.Computability.VPVNP.PairShrinkHiddenSeedBudget
import OAI.Computability.VPVNP.CompressorSlotState
import OAI.Computability.VPVNP.CompressorLevelCounts

/-!
# Child and hidden arguments of the selected shrinking prologue

One coefficient fixed by the schedule and its templates bounds the two
directory counts and the number of bits consumed by each native scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open Compression Compression.ShrinkMotif CompressorRecords CompressorRecords.ShrinkSlots
open LocalHistory NetworkKernel ShrinkRole

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K}

/-- Cover both directory counts and both coefficients for the payload widths. -/
noncomputable def prologueCoefficient (B : S.Templates) : ℕ :=
  max (max B.recordLimit (2 * slotDegree S * B.recordLimit))
    (max (ShrinkHiddenRows.stageCapacity S)
      (ShrinkHiddenRows.stageCapacity S * fieldFactor B.shrink))

/-- Bound the child arguments of the actual placement fiber and the absorbed
words of its selected layout, for every choice of the initial hidden values. -/
theorem selected_prologue_bounds (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
    (i : Fin S.steps) {g w : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (sel : X.ShrinkSelection B.shrink)
    (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
    (desc : ChildArguments.Descriptor w X)
    (order : desc.sites = List.ofFn fun j =>
      ((((shrinkPassReaders B f hf i rfl X).order sel).children v).entries j).val)
    (placeholder : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
      (internalLabel (ShrinkHiddenRows.widths X B.shrink sel) (selectedLayout X B.shrink sel)) v) :
    let C := prologueCoefficient B
    let seed := ShrinkHiddenSlots.rows X (selectedLayout X B.shrink sel)
      (ShrinkHiddenRows.widths X B.shrink sel) v placeholder
    desc.sites.length ≤ C ∧ ChildArguments.demand X desc.sites ≤ C * (X.maxWireWidth + 1) ∧
      seed.length ≤ C ∧ (ShrinkHiddenGuess.stream seed).length ≤ C * (X.maxWireWidth + 1) := by
  intro C seed
  obtain ⟨children, demand⟩ := ChildArguments.selected_budget B f hf i X sel v desc order
  obtain ⟨fields, bits⟩ :=
    ShrinkHiddenRows.scheduled_seed_bounds (selectedLayout X B.shrink sel) B i X sel v placeholder
  have degree : 2 ^ S.degreeExponent i.castSucc ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps + 1) => 2 ^ S.degreeExponent j)
      (Finset.mem_univ i.castSucc)).trans
      (le_max_right ..)
  have childBits : 2 * 2 ^ S.degreeExponent i.castSucc * B.recordLimit ≤ C :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 degree)).trans
      ((le_max_right ..).trans (le_max_left ..))
  exact ⟨children.trans ((le_max_left ..).trans (le_max_left ..)),
    demand.trans (Nat.mul_le_mul childBits (Nat.le_succ _)),
    fields.trans ((le_max_left ..).trans (le_max_right ..)),
    bits.trans (Nat.mul_le_mul_right _ ((le_max_right ..).trans (le_max_right ..)))⟩

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
