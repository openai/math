import OAI.Hierarchy.DescentDatedMaterialExtent
import OAI.Hierarchy.DescentMaterialReceptionROM
import OAI.Hierarchy.DescentOrdinaryMaterialScan
import OAI.Hierarchy.DescentOverlapBooks

namespace OAI
/-! # Public instruction and address parameters of the ordinary material program -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.Chronology DescentRawCablePanel DescentSIMDLookup DescentPackedColony
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure MaterialProgram where
  extent : MaterialExtent
  depot : DepotRAM.Shape
  setup : DepotRAM.Material.Setup

namespace MaterialProgram
variable (s : MaterialProgram)
local notation "e" => s.extent
local notation "fmt" => s.depot
def rankHeader (base : ℕ) (reverse : Bank) :=
  DonorChartBook.tables (e).oldHosts (e).oldGroups (e).oldLanes (breadth (fmt).degree) base reverse
def materialCharts (base w : ℕ) : NativePhase w :=
  let P:=breadth (fmt).degree
  ⟨DonorChartBook.install (e).oldHosts (e).oldGroups (e).oldLanes P base w,
    4+10*DonorChartBook.words (e).oldHosts (e).oldGroups (e).oldLanes P,
    DonorChartBook.image (e).oldHosts (e).oldGroups (e).oldLanes P base,
    @DescentStaticWordColumn.cheap _ _ _ _⟩
def materialJoin (base : ℕ) (parts reverse : Bank) (w : ℕ) :=
  RegisterJoin.phase (DepotRAM.totalBits fmt) (DepotRAM.chartBits fmt) (e).oldHosts (e).oldGroups (e).oldLanes w
    ((e).joinBase base) (.lookup parts .row) (context (s.rankHeader base reverse))
def joinBank (base : ℕ) :=
  RegisterJoin.bank (DepotRAM.totalBits fmt) (DepotRAM.chartBits fmt) (e).oldHosts (e).oldGroups (e).oldLanes ((e).joinBase base)
def materialSheets (base w : ℕ) := DepotRAM.Material.Sheets.phase fmt s.setup (e).oldHosts (e).oldGroups (e).oldLanes w
  ((e).observationsStart base) (s.joinBank base)
def materialJob (base : ℕ) : Overlap.Job :=
  ⟨DepotRAM.Material.Sheets.bank fmt (e).oldHosts (e).oldGroups (e).oldLanes ((e).observationsStart base),
    (e).fields*(e).oldHosts,(e).oldGroups,(e).oldLanes,(e).lanes*(e).blocks,(e).fieldBits⟩
def materialMaps (base w : ℕ) :=DepotRAM.Material.Route.Projection.stage (e).oldHosts (e).hosts (e).groups (e).lanes (e).reach
  (e).fieldBits (e).blocks s.setup.hostPitch ((e).projectionStart base) w

/-- The two input addresses are the original retained donor and the actual previous reverse-rank bank. -/
def materialAt (base : ℕ) (parts reverse : Bank) (w : ℕ) : NativePhase w :=
  ((((s.materialCharts base w).seq (s.materialJoin base parts reverse w)).seq (s.materialSheets base w)).seq
    ((s.materialJob base).phase ((e).overlapStart base) w)).seq (s.materialMaps base w)
def receivedBank (base : ℕ) (j : Fin (DepotRAM.Material.Sheets.count fmt)) : Bank :=
  let out:=(s.materialJob base).target ((e).overlapStart base)
  ⟨out.base+j.val*((e).oldHosts*chunks (e).oldGroups ((e).lanes*(e).blocks)),Nat.clog 2 ((e).oldHosts*chunks (e).oldGroups ((e).lanes*(e).blocks))⟩

end MaterialProgram
end
end Hierarchy.DescentDatedAddressBook

end OAI
