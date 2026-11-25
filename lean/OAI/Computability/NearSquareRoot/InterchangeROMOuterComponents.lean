import OAI.Computability.NearSquareRoot.InterchangeROMFamilyComponents
import OAI.Computability.NearSquareRoot.InterchangeROMOuterSelected
import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulersTemplate

/-! # Concrete native component certificates for the selected family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code NearSquareRoot.Interchange
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMFamily

/-- All three operands are specified commands computed from the numeric
template. The two physical bank passes have one joint degree; the Hermite
program retains its own absolute compiler degree and literal child ledger. -/
theorem native_components (F : InterchangeROMFront.Core) :
    ∃ kb kc ku : ℕ, ComponentRuns F templateEnter templateLeave kb kc ku := by
  obtain ⟨kb,B,_,wires⟩ := template_wires
  obtain ⟨kc,C,_,middle⟩ := selected_main
  refine ⟨kb,kc,kb,?_⟩
  intro j t x h
  refine ⟨B x,C x,B x,?_⟩
  intro parent q good hw
  obtain ⟨enter,leave⟩ := wires x h q good hw parent
  refine ⟨enter,?_,leave⟩
  intro u
  obtain ⟨ledger,length,children,run⟩ := middle x h q good hw u
  exact ⟨ledger,length,children,run parent⟩

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
