import OAI.Hierarchy.DescentDatedOrdinaryArgumentExit

namespace OAI
/-! The early native donor counter is below the seven writer banks. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem donor_before_arguments (floor : ℕ) :
    v.donorEnd floor ≤ v.finalChart.out (v.metaEnd floor) := by
  obtain ⟨material,peer,signed⟩:=v.signed_stage_paid floor
  have source : v.signedEnd floor≤v.birthStart floor:=by
    change _≤v.signedEnd floor+v.ingressWords+v.reference.extent
    omega
  have born : v.birthStart floor≤v.vectorStart floor:=by
    rw [vectorStart,v.bornBook.affine];exact Nat.le_add_right ..
  have raster : v.endAddress floor≤v.rasterEnd floor:=by
    rw [rasterEnd,StageVenueTail.OrdinaryRaster.translated];exact Nat.le_add_right ..
  have venue : v.rasterEnd floor≤v.metaStart floor:=by
    change _≤v.venue.endAddress _
    rw [v.venue.translates];exact Nat.le_add_right ..
  have metadataBound : v.metaStart floor≤v.metaEnd floor:=by
    rw [metaEnd,v.metadata.ordinary_translate];exact Nat.le_add_right ..
  have writer : v.metaEnd floor≤v.finalChart.out (v.metaEnd floor):=by
    change _≤v.metaEnd floor+_+_
    omega
  exact material.trans (peer.trans (signed.trans (source.trans (born.trans ((v.vector_before floor).trans
    ((v.routed_le floor).trans ((v.resolver.floor_le _).trans (raster.trans (venue.trans (metadataBound.trans writer))))))))))

end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
