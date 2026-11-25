import OAI.ThreeFlat.Diagonal.ShrinkIssuedWidth
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.PhysicalStateWidth

namespace OAI
/-! # Maximum successor width of a physical binary shrink -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking PhysicalShrink
open scoped Classical
noncomputable section

variable {F : Type} [Field F]

def shrinkWidthFactor (T : ShrinkMotif.Table F) (s : ℕ) : ℕ :=
  shrinkMotifWidthFactor T (2*(2^s)+1) (2^s)

private theorem widthBound_lanes {d l l' D rem : ℕ} (h : l=l') (A : State d l)
    (R : Move F (h ▸ A : State d l') D rem) {C : ℕ} (H : R.WidthBound C) :
    (Move.recastInputLanes h A R).WidthBound C := by
  cases h
  exact H

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem shrinkMove_width {d lanes rem hbits tags D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P = changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).WidthBound
      (shrinkMotifWidthFactor T (2*d+1) d) := by
  unfold shrinkMove
  apply Move.widthBound_degree
  intro i
  apply State.maxWidth_le
  intro e
  have hc : 2 ≤ 2*d+1 := by omega
  let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm i
  let len := issued T P (oldWidth A u) code hc hist
  let side := ShrinkMotif.chooseWidths len
  let n := parallel (2*d+1) d D
  let cover := allPieceSlots P binary_neg good side n order hc (padding (2*d+1) d D)
  let amount (j : CrossEdge P side) := len j.1 j.2
  exact SlotRefinement.actualWidth_le (fun j => n (typeIndex P binary_neg good side j))
    amount cover (fun j => PhysicalShrink.issued_le P (oldWidth A u) T code hc
      (fun a => A.width_le_maxWidth ((StageAddress.splitEdge u).symm a)) hist j.1 j.2) e

theorem shrinkRaw_width (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small A).WidthBound (shrinkWidthFactor T s) := by
  unfold shrinkRaw
  apply shrinkMove_width

theorem shrinkBinary_width (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    (shrinkBinary T s D rem hD small A).WidthBound (shrinkWidthFactor T s) := by
  unfold shrinkBinary
  apply widthBound_lanes
  exact shrinkRaw_width T s D rem hD small _

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
