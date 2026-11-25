import OAI.Hierarchy.DescentSeedHubTrivalence
import OAI.Hierarchy.DescentSeedHistory
import OAI.Hierarchy.DescentNativeInput
import OAI.Hierarchy.DescentSeedSiteGeometry

namespace OAI
/-! # The primitive census tag of an original vertex or exterior host -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentKernelHistory DescentSeedRoot DescentInitialHost DescentPhysicalSplit Catalyst CorrectionBatch
open Computability.BorderVNP.Crossing
noncomputable section
variable {F : Type} [Field F] {n gates s : ℕ}
variable (X : Approximation F n gates) (R : ℕ) (c : (initialGroup X R s).Choice)
local notation "N" => X.network.copyGraph
local notation "H" => hubbed N

def seedRole (j : Fin R) : Vertex X → SeedTag s
  | .inl v=>.inl (censusRole H (hubbed_trivalent N (physical_output X).1) (.inl v) (c j (.inl v)))
  | .inr _=>.inr ()

end
end Hierarchy.DescentPrimitivePalette

end OAI
