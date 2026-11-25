import OAI.Hierarchy.DescentTerminalRoleWords
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # Sizes of the six original terminal role-table inputs -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentPrimitivePalette
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec)

def originalRoleBits (S:AtomSchedule) (p drift:ℕ) (field:Fin 6) :=
  let colors:=DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
  DescentTerminalCombinedRole.width colors (max 8 (2^S.capGain))
    (NativeBranch.privateSlotCapacity G S drift) p drift field*(S.epochPower^S.localTokenExponent)*
    S.groupCount S.length

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
