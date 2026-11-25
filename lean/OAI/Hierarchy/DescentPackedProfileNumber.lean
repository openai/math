import OAI.Hierarchy.DescentTerminalProfileCodes

namespace OAI
namespace Hierarchy.DescentPacking.PackedMatch.LayoutSum
open DescentSixParty DescentTerminalEpochFlags
noncomputable section
def profileCode (C : ℕ) : Profile C↪Fin (alphabet C) :=
  (Function.Embedding.subtype _).trans finFunctionFinEquiv.toEmbedding

end
end Hierarchy.DescentPacking.PackedMatch.LayoutSum

end OAI
