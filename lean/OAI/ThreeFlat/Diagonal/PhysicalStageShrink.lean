import OAI.ThreeFlat.Diagonal.PhysicalStage
import OAI.ThreeFlat.Diagonal.PhysicalShrink
import OAI.ThreeFlat.Diagonal.ShrinkTagPadding

namespace OAI
/-! # A full shrinking pass as an adaptive transition on physical lifted states -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking CompressorPacking.PhysicalShrink HistoryContraction
open scoped BigOperators Classical
noncomputable section
variable {d lanes rem hbits tags D : ℕ} {F : Type} [Field F]
private abbrev cpos (hd : 0<d) : 2≤2*d+1 := by omega

variable (T : ShrinkMotif.Table F) (A : State d lanes)
  (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
  (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
  (agree : StageAddress.packedGraph P=changeLanes A.graph u)
  (good : TagConditions P.slots (shift P) P.offset)
  (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
  (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
  (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ)

abbrev oldWidth := A.width ∘ (StageAddress.splitEdge u).symm
abbrev shrinkBranches := Hists T P (oldWidth A u) code (cpos hd)

/-- Restore the association of base, tag and residual lane used by the physical slot graph. -/
private def shrinkChart (V T L : Type) : (V×T)×L ≃ Site V T L := Equiv.prodAssoc V T L

/-- The output state is constructed from its retained supply slots, adjacent-tag padding, and
actual balanced per-slot widths. The source graph is relabelled via the fixed lane partition. -/
def shrinkMove : Move F A D rem := by
  let c := 2*d+1
  let n := parallel c d D
  let pad := padding c d D
  let old := oldWidth A u
  let tag := Native.adjacentMask tagSize
  have nonzero := Native.adjacent_ne tagSize
  let terms := shrinkBranches T A u P hd code
  let enum : Fin (Fintype.card terms) ≃ terms := (Fintype.equivFin terms).symm
  let J := StageAddress.shrinkInputIso A.graph A.chart u P agree A.width
  let rules := J.rewrite (PhysicalShrink.step T P old code (cpos hd) hd hD small binary_neg good order tag nonzero enum)
  have degree : usedDegree n c d+pad=D := degree_eq (cpos hd) hd hD
  suffices Move F A (usedDegree n c d+pad) rem by exact degree ▸ this
  let len (i : Fin (Fintype.card terms)) := issued T P old code (cpos hd) (enum i)
  let side (i : Fin (Fintype.card terms)) := ShrinkMotif.chooseWidths (len i)
  let graph (i : Fin (Fintype.card terms)) := CompressorRefresh.union
    (shrinkingGraph P (side i) n order (cpos hd) binary_neg good) (tagPadding tag nonzero pad)
  let width (i : Fin (Fintype.card terms)) := SlotRefinement.actualWidth
    (fun e => n (typeIndex P binary_neg good (side i) e))
    (fun e : CrossEdge P (side i) => len i e.1 e.2) (allPieceSlots P binary_neg good (side i) n order (cpos hd) pad)
  refine ⟨rules, fun i => {
    Base := A.Base × BitWord tags
    order := productOrder A.order (Native.tagOrdinal tags)
    Site := Site A.Base (BitWord tags) (BitWord rem)
    chart := shrinkChart _ _ _
    graph := graph i
    width := width i }, ?_⟩
  intro i
  rfl

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
