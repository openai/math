import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import OAI.Hierarchy.DescentDatedPrimitiveExtent

namespace OAI
/-! Fit the true old donor chips, printed labels and published origins at the actual funded ordinary pitches. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPrimitivePalette DescentOrdinaryPrimitiveCheckpoint
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem funded_primitive_widths (A : ArgumentEntry v) (other : ℕ) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    W.paletteShape.primitiveBits*W.bornBook.lanes≤v.payload/2 ∧
      2*W.bornBook.chipBits*W.bornBook.lanes≤v.payload/2 ∧
      (W.paletteShape.originBits*W.resolver.nodes)*W.vector.lanes≤v.payload/2:=by
  intro extra W
  let M:=W.bornBook.lanes
  let T:=W.vector.lanes
  let b:=W.paletteShape.primitiveBits
  let origins:=W.paletteShape.originBits*W.resolver.nodes
  have available : max (max W.bornBook.chipBits (W.bornBook.bits*W.resolver.nodes)) b*M≤v.payload/4:=
    (v.funded_argument_widths A other 14).1
  have tokenFits : b*M≤v.payload/4:=(Nat.mul_le_mul_right M (Nat.le_max_right _ _)).trans available
  have chips : (W.bornBook.chipBits*1+W.bornBook.chipBits)*M≤v.payload/4:=(v.funded_argument_widths A other 6).1
  have recorded : (origins*1+origins)*T≤v.payload/4:=(v.funded_argument_widths A other 12).2.2
  have original : origins*T≤v.payload/4:=(Nat.mul_le_mul_right T (Nat.le_add_left _ _)).trans recorded
  have chipEq : 2*W.bornBook.chipBits=W.bornBook.chipBits*1+W.bornBook.chipBits:=by ring
  change b*M≤v.payload/2 ∧ 2*W.bornBook.chipBits*M≤v.payload/2 ∧ origins*T≤v.payload/2
  rw [chipEq]
  omega

/-- The late primitive pass reads the padded host-rectangle role bank already emitted by the inlet. -/
theorem funded_primitive_prior (A : ArgumentEntry v) (other : ℕ)
    (width : A.roleBits=printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor) :
    let W:=v.withFundedArguments (max (v.fullArgumentUnit A) other) A
    (W.paletteShape.primitiveBits*W.reference.oldNodes)*W.paletteShape.priorLanes≤v.payload/2:=by
  intro W
  let extra:=max (v.fullArgumentUnit A) other
  have measured : (A.roleBits*W.reference.oldNodes)*W.rasterLanes≤v.payload/4:=
    (v.funded_argument_widths A other 1).1
  change (printedBits v.gadget v.palette.seedWidth v.palette.grainLimit v.palette.rotor*W.reference.oldNodes)*W.rasterLanes≤_
  rw [←width]
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
