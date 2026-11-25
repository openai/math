import OAI.Hierarchy.DescentSeedNativeHardware
import OAI.Hierarchy.DescentSeedWideFlagProgram
import OAI.Hierarchy.DescentSeedNodeChart
import OAI.Hierarchy.DescentDatedNodeMetadataSeed
import OAI.Hierarchy.DescentPrivateHeaderCheap
import OAI.Hierarchy.ProtocolRAMSumScoresCheap
import OAI.Hierarchy.DescentAtomSchedule

namespace OAI
/-! # The original ballot validator with a short dictionary and a wide address word -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentCompiler DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open DescentSeedInitialTable DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F : Type} [Field F] {S : AtomSchedule} {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header payload w : ℕ)
local notation "g₀" => S.groupCount 0
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "core" => DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w
local notation "check" => DescentWideSeedFlags.check X S.copies l.seedWidth payload w
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload

def wideNode := ((((check).seq core).seq (DescentPrivateHeader.clearHeader w header)).seq
  ((chart).seedProgram top w Q))

def wideTicks := 4+(entries+1)*66+DescentDatedSeedStartup.clock X l H g₀ k+10+(chart).seedTicks

theorem wide_cheap : CheapCode (wideNode X digits publicWide l header payload w) :=by
  let clear := DescentPrivateHeader.clearHeader w header
  let metadata := (chart).seedProgram top w Q
  have counted : CheapCode check := PruneFlag.cheap _ _ _ _ _
  have installed : CheapCode core := (hardware X (Equiv.refl _) digits hs l w).1
  exact @cheap_seq w (((check).seq core).seq clear) metadata
    (@cheap_seq w ((check).seq core) clear (@cheap_seq w check core counted installed)
      (DescentPrivateHeader.initialize_cheap w header))
    ((chart).seedCheap top w Q)

/-- The bill counts only native operations and executable instructions. The
original proposal and its immutable ROM can be paid once by their own input invoice. -/
theorem wide_price (active : 0<chunks g₀ l.operandLanes) :
    wideTicks (S:=S) (H:=H) (k:=k) X l payload+
      7*DescentStaticWordColumn.names (wideNode X digits publicWide l header payload w) ≤
      1300+66*entries+1600*(top-l.base+1)+115*((chart).names*(chart).rows) := by
  have signed:=hardware X (Equiv.refl _) digits hs l w
  have data:=tariff_increment X l H g₀ k active
  have clocks : DescentDatedSeedStartup.clock X l H g₀ k=clockBound X l H g₀ k :=by
    unfold DescentDatedSeedStartup.clock operandClock clockBound
    rw [Signed.Plane.clock_eq]
  have stage:=(chart).seedPrice top w Q
  have clear : DescentStaticWordColumn.names (DescentPrivateHeader.clearHeader w header)=15 :=by
    change DescentStaticWordColumn.names (scan w header 1 (.lit 0))=15
    rw [DescentStaticWordColumn.names_scan]
    decide
  unfold wideNode wideTicks
  rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,
    DescentWideSeedFlags.names,clear,clocks]
  omega

end
end Hierarchy.DescentDatedSeedStartup.Input

/-! # Native code, output and instruction count after the original ballot check -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentCompiler DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open DescentSeedInitialTable DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
open ThreeFlat.RAM PhysicalProcedure
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
local notation "core" => DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w
def afterCount (w : ℕ) : Procedure w :=
  ((DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w).seq
    (DescentPrivateHeader.clearHeader w header)).seq ((chart).seedProgram top w Q)

def afterCountTicks := DescentDatedSeedStartup.clock X l H g₀ k + 10 + (chart).seedTicks


end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
