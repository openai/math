import OAI.Hierarchy.DescentSeedCountImage
import OAI.Hierarchy.DescentSeedTokenProgram

namespace OAI
/-! Exact final seed RAM including published roles and palette pages. -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentColonies DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
  {k cp p H : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "combine" => DescentDatedSeedStartup.Primitive.image X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
def completeImage {w : ℕ} (m : Memory w) := (combine) (afterCountImage X digits publicWide l header m)
end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
