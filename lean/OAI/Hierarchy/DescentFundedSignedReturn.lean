import OAI.Hierarchy.DescentNamedReturnFunding
import OAI.Hierarchy.DescentFundedClipChoice

namespace OAI
/-! # The complete signed prefix in the installed twelve-entry argument date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentDatedAddressBook ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem funded_return_program (extra : ℕ) (args : ArgumentEntry v) (floor : ℕ) :
    (v.withFundedArguments extra args).signedProgram floor=v.signedProgram floor :=rfl

theorem funded_return_prefix (extra : ℕ) (args : ArgumentEntry v) (floor w : ℕ) (parts adj : Bank)
    (old : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) :
    (v.withFundedArguments extra args).signedReturnPrefix floor w parts adj old input=
      v.signedReturnPrefix floor w parts adj old input :=rfl

theorem funded_return_charge (extra : ℕ) (args : ArgumentEntry v) (floor w : ℕ) (parts adj : Bank)
    (old : DescentOrdinaryVenueReturn.Sources) (input : Dated.Operands) :
    ((v.withFundedArguments extra args).signedReturnPrefix floor w parts adj old input).wordInvoice=
      (v.signedReturnPrefix floor w parts adj old input).wordInvoice :=rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
