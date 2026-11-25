import OAI.Hierarchy.DescentSeedNodeChart
import OAI.Hierarchy.DescentDatedSeedPublicCode
import OAI.Hierarchy.DescentDatedNodeMetadataSeed

namespace OAI
/-! # The public seed constructor and packed previous gate metadata -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentCompiler DescentSeedRoot DescentPackedSeed DescentInitialHost DescentSeedInitialTable
open DescentSIMDLookup DescentColonies Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {S : AtomSchedule} {k cp p H w : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header : ℕ)
local notation "g₀" => S.groupCount 0
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top

def nodeProgram := (publicProgram (A:=A) X digits publicWide l header (w:=w)).seq ((chart).seedProgram top w Q)

theorem node_cheap : CheapCode (nodeProgram (A:=A) X digits publicWide l header (w:=w)) := by
  intro P' R' K' pc reg pub exit i
  exact cheap_seq (public_cheap (A:=A) X digits publicWide l header (w:=w))
    ((chart).seedCheap top w Q) pc reg pub exit i

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
