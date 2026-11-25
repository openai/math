import OAI.Hierarchy.DescentDatedFundedCompactRoom

namespace OAI
/-! # Locations of the saved rotation and the ballot count in an ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem reel_cells (root : ℕ) :
    let stage:=v.stageStart root
    let rotation:=v.area.flagEnd v.old stage+2^v.k
    root≤v.countAddr root ∧ v.countAddr root<v.fullEnd root ∧
      root≤rotation ∧ rotation<v.fullEnd root :=by
  intro stage rotation
  have start : root≤ stage:=by
    change root≤v.profileRepack.endAddress root
    rw [v.profileRepack.translate]
    exact Nat.le_add_right ..
  have offset:=v.area.rotation_add v.old 0 stage
  change v.area.rotationEnd v.old (stage+0)=stage+v.area.rotationEnd v.old 0 at offset
  rw [Nat.add_zero] at offset
  have plus : rotation+1=v.area.rotationEnd v.old stage:=rfl
  have nonempty : 0<v.area.rotationEnd v.old 0:=Nat.zero_lt_succ _
  have donor : v.area.rotationEnd v.old stage≤v.donorEnd stage:=by
    change _≤v.ticket.wholeDonorEnd v.short v.profile (2^v.level) v.payload (v.area.rotationEnd v.old stage)
    rw [v.ticket.wholeDonorEnd_translate]
    exact Nat.le_add_right ..
  have stored : v.donorEnd stage≤v.endAddress stage:=by
    have norms:=v.arguments_extent stage
    change v.normalizedEnd stage=v.vector.endAddress (v.donorEnd stage)+v.argumentExtra at norms
    rw [DescentOperandVectorArena.affine] at norms
    change _≤v.resolver.endAddress (v.normalizedEnd stage)
    rw [v.resolver.affine]
    omega
  have raster : v.endAddress stage≤v.rasterEnd stage:=by
    rw [rasterEnd,StageVenueTail.OrdinaryRaster.translated]
    exact Nat.le_add_right ..
  have stop := raster.trans (v.raster_below_full root)
  have last := v.count_written root
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
