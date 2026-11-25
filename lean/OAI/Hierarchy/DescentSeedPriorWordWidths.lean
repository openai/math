import OAI.Hierarchy.DescentSeedReaderWidths
import OAI.Hierarchy.DescentSeedPrintedPitch

namespace OAI
/-! # The two original predecessor banks fit the true first ordinary retile -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSixParty DescentCompiler DescentPrimitivePalette
variable {F : Type} [Field F]
theorem seed_data (D : PoweredGadget F) (op : RotorSpec) (S : AtomSchedule)
    (h k tail g p drift degree f quota base field wire hist Z : ℕ) :
    let l:=selectedLayout D S h k tail g p drift degree f quota base field wire hist
    l.operandBits*l.operandLanes ≤ h/2 ∧
      printedBits D l.seedWidth Z op*Primitive.paletteLanes D op l.seedWidth Z h k ≤ h/2 :=
  ⟨chosen_operand_half D S h k tail g p drift degree f quota base field wire hist,Primitive.chosen_printed_half D op _ Z h k⟩

end Hierarchy.DescentDatedSeedStartup

end OAI
