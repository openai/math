import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentSeedNativeStartup
import OAI.Hierarchy.DescentDatedNodeMetadataSeed
import OAI.Hierarchy.DescentSeedNodeChart
import OAI.Hierarchy.DescentPrivateHeader

namespace OAI
/-! Exact memory after the seed census, private header clear and the two metadata pages. -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentCompiler DescentSeedRoot DescentInitialHost DescentColonies Catalyst Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header : ℕ) {w : ℕ}
local notation "g₀" => S.groupCount 0
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
def afterCountImage (m : Memory w) :=
  (chart).seedImage top Q (DescentPrivateHeader.initialized header (output X (Equiv.refl _) digits hs l m))
end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
