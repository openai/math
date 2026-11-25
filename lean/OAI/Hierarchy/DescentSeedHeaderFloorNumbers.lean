import OAI.Hierarchy.DescentSeedTokenSourceLayout
import OAI.Hierarchy.DescentSeedTokenLayout
import OAI.Hierarchy.DescentSeedPrintedPitch
import OAI.Hierarchy.DescentPackedEpochShelfLayout

namespace OAI
/-! # The exact seed transposition end and row count of each dated shelf -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open Catalyst DescentSeedRoot
noncomputable section
variable {F : Type} [Field F] {c p : ℕ} (X : Approximation F c p)
variable (R s payload k H G M base : ℕ)
set_option quotPrecheck false
local notation "O" => Fintype.card (Old X)
local notation "A" => DescentPackedSeed.Primitive.pieces payload s
local notation "a" => DescentPackedSeed.Primitive.roleBits s
local notation "splitAt" => DescentPackedSeed.Primitive.Source.finish X R s payload base

def initialEnd := DescentSeedTokenTransposition.endAddress splitAt O H G (2^k) a A M
end
end Hierarchy.DescentDatedSeedStartup.Primitive

namespace Hierarchy.DescentPackedEpochShelves
open DescentPackedProfileTape
variable {A : Type}
def stepRows (r : ℕ) (p : Shelf A) := slots p.src.seats r+2
end Hierarchy.DescentPackedEpochShelves

end OAI
