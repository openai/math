import OAI.Hierarchy.DescentDatedFundedCompactRoom
import OAI.Hierarchy.DescentDatedSignedSpace

namespace OAI
/-! # Address validation at the original signed output within the complete registered date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The signed output is retained through the operand scatter and the final returned count. -/
theorem signed_before_full (root : ℕ) :
    v.signedEnd (v.stageStart root)≤v.fullEnd root :=by
  let base:=v.stageStart root
  have afterRefs : v.signedEnd base≤v.birthStart base:=by
    change v.signedEnd base≤v.signedEnd base+v.ingressWords+v.reference.extent
    omega
  have afterBirths : v.birthStart base≤v.vectorStart base:=by
    change v.birthStart base≤v.bornBook.endAddress (v.birthStart base)
    rw [v.bornBook.affine (v.birthStart base)]
    exact Nat.le_add_right ..
  have operands : v.normalizedEnd base≤v.endAddress base:=by
    change v.normalizedEnd base≤v.resolver.endAddress (v.normalizedEnd base)
    rw [v.resolver.affine (v.normalizedEnd base)]
    exact Nat.le_add_right ..
  have raster : v.endAddress base≤v.rasterEnd base:=by
    change _≤StageVenueTail.OrdinaryRaster.roof v.area v.venue v.rasterLanes (v.endAddress base)
    rw [StageVenueTail.OrdinaryRaster.translated _ _ _ (v.endAddress base)]
    exact Nat.le_add_right ..
  exact afterRefs.trans (afterBirths.trans ((v.vector_before base).trans
    ((v.routed_le base).trans (operands.trans (raster.trans (v.raster_below_full root))))))

theorem signed_guard_span (root : ℕ) :
    v.signedGuard (v.stageStart root)-root ≤ v.fullCeiling+
      (v.signedGuard (v.stageStart root)-v.signedEnd (v.stageStart root)) :=by
  have cap:=(v.full_spent root).2.1
  have old:=v.signed_before_full root
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
