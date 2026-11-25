import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProtocolRAMCatalystStripOwnerCost
import OAI.Hierarchy.ProtocolRAMCatalystArchiveGrowth

namespace OAI
/-! # Fixed resources of the actual dated owner and route selectors -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h



local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs

/-- The time coefficient and text length use the same public integer at every height. -/
def wideOwnerRouteBill :=
  let n:=18*(D-1)+1
  let roles:=max (Fintype.card (StripDirectory.PayloadRole n k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
  let factor:=ownerRowFactor D k v.sampler.degree v.depth roles
  let cost:=ownerWork roles k (ownerColumnCost D k v.wideJobs)
  let op:=operationBound n k v.wideJobs
  let time:=(4+last*(4+factor*(2*cost+4)))+(12+(2*CatalystArchive.slotFactor D k)*(22+2*op))
  let text:=(15+last*(11+4*cost))+(65+4*op)
  time+text

/-- The ledger is queried at each dated port. The same two route passes in
the terminal procedure visit the original catalogue row of every wire slot. -/
theorem wide_owner_route_resources {count : ℕ} :
    ProtocolRAM.clock ((L).scans v.mesh count)+ProtocolRAM.clock routes≤v.wideOwnerRouteBill*2^h ∧
      listText ((L).scans v.mesh count)+listText routes≤v.wideOwnerRouteBill := by
  let n:=18*(D-1)+1
  let roles:=max (Fintype.card (StripDirectory.PayloadRole n k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
  let factor:=ownerRowFactor D k v.sampler.degree v.depth roles
  let cost:=ownerWork roles k (ownerColumnCost D k v.wideJobs)
  let op:=operationBound n k v.wideJobs
  have phase : N=n := CoreCatalogue.total_stages h D
  have work (e : Event) : (clamp count ((L).term e)).work≤cost := by
    have read:=ledger_owner_work s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride) count e
    have cap : ownerWork (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))) k
        (ownerColumnCost D k v.wideJobs)=cost := by rw [phase]
    exact read.trans_eq cap
  have visits (e : Event) : (L).rows e≤factor*2^h := by
    have read:=ledger_owner_rows s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride) e
    have cap : ownerRowFactor D k v.sampler.degree v.depth
        (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h=factor*2^h := by
      rw [phase]
    exact read.trans_eq cap
  have ownerClock:=(L).time_bound v.mesh count (factor*2^h) cost (fun e _=>⟨visits e,work e⟩)
  have ownerText:=(L).text_bound v.mesh count cost (fun e _=>work e)
  have routeClock:=CoreRoute.clock_bound (S:=v.sampler) (z:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    (routeBanks start cnt r) g old
  have routeText:=CoreRoute.text_bound (w:=0) (S:=v.sampler) (z:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs)
    (routeBanks start cnt r) g old
  have rk : operationBound N k v.wideJobs=op := congrArg (fun u=>operationBound u k v.wideJobs) phase
  rw [rk] at routeClock
  rw [text_passes,rk] at routeText
  have slots:=slot_count h D k (Nat.two_pow_pos _)
  have routeBound:=Nat.mul_le_mul_right (22+2*op) (Nat.mul_le_mul_left 2 slots)
  have scale (a : ℕ) : a≤a*2^h := by simpa using Nat.mul_le_mul_left a (Nat.two_pow_pos h)
  let cpu:=(4+last*(4+factor*(2*cost+4)))+(12+(2*CatalystArchive.slotFactor D k)*(22+2*op))
  let txt:=(15+last*(11+4*cost))+(65+4*op)
  have size : v.wideOwnerRouteBill=cpu+txt := rfl
  change ProtocolRAM.clock ((L).scans v.mesh count)+ProtocolRAM.clock routes≤v.wideOwnerRouteBill*2^h ∧
    listText ((L).scans v.mesh count)+listText routes≤v.wideOwnerRouteBill
  rw [size]
  constructor
  · apply Nat.le_trans (Nat.add_le_add ownerClock routeClock)
    refine le_trans ?_ (Nat.mul_le_mul_right (2^h) (show cpu≤cpu+txt from Nat.le_add_right ..))
    dsimp only [cpu]
    nlinarith only [scale (4+last*4+12),routeBound]
  · exact (Nat.add_le_add ownerText routeText).trans (Nat.le_add_left ..)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
