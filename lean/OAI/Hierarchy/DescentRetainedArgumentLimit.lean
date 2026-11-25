import OAI.Hierarchy.DescentPrivateShapeNumbers

namespace OAI
/-! The previous argument count and its drift-scaled width on the original retained register. -/
namespace Hierarchy.DescentSixParty.AtomSchedule
open DescentCompiler
noncomputable section
variable {F : Type} [Field F] (S : DescentCompiler.AtomSchedule) (G : PoweredGadget F)

def retainedArguments := S.epochPower^(operandExponent G S)
def retainedArgumentsAt (drift : ℕ) := (drift+1)*retainedArguments S G

end
end Hierarchy.DescentSixParty.AtomSchedule


namespace Hierarchy.DescentCompiler.AtomSchedule
export Hierarchy.DescentSixParty.AtomSchedule (retainedArguments retainedArgumentsAt)
end Hierarchy.DescentCompiler.AtomSchedule

end OAI
