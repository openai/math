import OAI.ThreeFlat.Diagonal.PhysicalShrinkFamily
import OAI.ThreeFlat.Diagonal.CompressorArcImage
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # The actual binary shrinking move's old graph in the physical RAM tables -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking Native
open scoped Classical BigOperators
noncomputable section

private theorem laneChart {B L : Type} {n v a b : ℕ} {G : LiftedSlots B n L}
    {base : B ≃ Fin v} {old : L ≃ Fin a} {new : L ≃ Fin b} {C : SlotImage.Columns} {mem : ℕ → ℕ}
    {w : SlotImage.Edge B L n → ℕ} (stored : SlotImage.Stored G base old C mem w)
    (ord : ∀ x,(new x).val=(old x).val) : SlotImage.Stored G base new C mem w := by
  have size : a=b := by simpa using Fintype.card_congr (old.symm.trans new)
  refine ⟨stored.rowCount,?_,?_⟩
  · intro p rev f
    rw [stored.graph]
    fin_cases f
    · rfl
    · rfl
    · exact (ord _).symm
  · intro e
    simpa only [SlotImage.edgeOrdinal,ord,size] using stored.widthWord e

private theorem state_cast {d i j : ℕ} (eqv : i=j) (A : State d i)
    (C : SlotImage.Columns) (mem : ℕ → ℕ)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal i) C mem A.width) :
    let B := (eqv ▸ A : State d j)
    SlotImage.Stored B.graph B.order (tagOrdinal j) C mem B.width := by cases eqv; exact old

variable (s rem : ℕ) (A : State (2^s) (shrinkCharge s+rem))

/-- Reassociate the public input lane budget and split the actual old bits
into colors, consumed slot, tag and residual binary lane. No old table data
is regenerated when this stage becomes current. -/
theorem shrinkImage (C : SlotImage.Columns) (mem : ℕ → ℕ)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) C mem A.width) :
    SlotImage.Stored (StageAddress.packedGraph (shrinkRecordPacking s rem A)) (shrinkRecordState s rem A).order
      (Demand.laneOrdinal (shrinkRecordPacking s rem A)) C mem
      (fun p=>shrinkRecordWidth s rem A (packedAddress p)) := by
  let A' := shrinkRecordState s rem A
  let P := shrinkRecordPacking s rem A
  let u := shrinkRecordLane s rem
  have h : shrinkCharge s+rem=(2*(2^s)+1)+(s+(tagBits (2^s)+rem)) := by simp [shrinkCharge,Nat.add_assoc]
  have hold := state_cast h A C mem old
  have cut := SlotImage.changeLanes_stored hold u
  change SlotImage.Stored (changeLanes A'.graph u) A'.order (Demand.laneOrdinal P) C mem _
  apply laneChart cut
  intro z
  obtain ⟨x,rfl⟩ := u.surjective z
  rw [Demand.split_lane_ordinal P (fun _=>rfl)]
  simp [u,shrinkRecordLane]


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
