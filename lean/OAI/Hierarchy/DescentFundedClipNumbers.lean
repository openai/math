import OAI.Hierarchy.DescentDatedOrdinaryRasterNumbers
import OAI.Hierarchy.DescentOrdinaryVenueClipNumbers

namespace OAI
/-! # The native clipping choice made by the current ordinary scheduler -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryVenueIngress DescentPackedActorMask DescentSIMDLookup
noncomputable section

/-- Per-lane keys for the quantity table, resident mask and combined paid-actor table. -/
def fundedUnitAt (a : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary) (paid : ℕ) :=
  let D:=StageVenueTail.OrdinaryRaster.paths a*2^a.k
  let A:=actors D a.cap
  max (paid*D+paid) (max (StageVenueTail.OrdinaryRaster.nameBits a*A) (1*A+paid*D))

/-- The public chart, including its register shape, matcher amount, source
pitches and paid census precision, determines the entire clipped receiver. -/
def fundedClipAt (a : DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (socket : DescentRawCablePanel.DepotRAM.Shape) (donorAmount paid extra : ℕ) : Clip :=
  ⟨⟨socket,a.H,a.G,0,a.k,a.profile,DescentHostDegree.gainExponent 20 a.D,
    DescentOrdinaryVenueReturn.shapeSlots a.D,StageVenueTail.OrdinaryRaster.shapes a⟩,
    a.payload,lanes a.payload donorAmount,a.lanesAt,max (fundedUnitAt a paid) extra⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
