import OAI.Hierarchy.DescentDatedPrimitiveExtent
import OAI.Hierarchy.DescentOrdinaryPaletteBankFloor

namespace OAI
/-! Each durable primitive page starts after the beginning of the emitted operand suffix. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
theorem primitive_bank_lower {F P : Type} [Field F] (v : PhysicalOrdinary F P) (operandStop : ℕ)
    (x : Fin v.paletteShape.blocks) : operandStop≤(v.primitiveBank operandStop x).base :=
  let earlier:=DescentOrdinaryPaletteBirth.order v.bornBook operandStop
  (earlier.1.trans earlier.2).trans (v.paletteShape.bank_lower _ x)
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
