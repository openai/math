import OAI.Hierarchy.DescentSeedTokenNumbers

namespace OAI
/-! # Shape and number of entries in the original shared seed role table -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot
noncomputable section
abbrev Plan := Σ m : Fin 4,(Fin m.val→Bool)→Fin 8
def cols (s M : ℕ) := Fintype.card Plan*2^(digitsNeeded s*8*M)
end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
