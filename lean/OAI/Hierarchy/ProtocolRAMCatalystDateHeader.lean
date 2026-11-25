import OAI.Hierarchy.ProtocolRAMCatalystStripDates
import OAI.Hierarchy.ProtocolRAMCoreRoutePaid
import OAI.Hierarchy.ProtocolRAMCalendarEconomicHistory

namespace OAI
/-! # The core route and strip header read by every date of the original calendar -/

namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CatalystArchive ProbeStage CoreBoard ColumnWires StockCommit
open StripDirectory BoughtSockets
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k q depth K R H M phases X Y steps : ℕ}
local notation "N" => Stages z (2^W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))
local notation "bits" => Native.wordBits z (2^W) Native.copies
variable (F : Type*) [Field F] [Nonempty (Fin k)] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z (2^W) k q depth) (c : Mesh)
  (b : CatalogueRows.Board)
local notation "n" => (c.inject+c.cool)*c.outerFuel
variable (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (π : Equiv.Perm (Fin (2^z))) (groups : Fin G.oldGroups≃AllGroups z (2^W))
  (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) G.height)

structure DatedBoard (a : Attempt) (m : Memory bits) : Prop where
  columns : ColumnROM.Tables z W k n G.column G.directory.remapBase G.directory.sitesBase G.directory.superBase groups packed π m
  input : Native.Resident (Native.initialOutput z) m (fun u : Fin (2^z)=>(π u).val)
  strata : (BoughtSockets.Public.keyHead s.sampler G.column z W k depth).Loaded m
  port : (header F (withPorts s c b G) a).Loaded m

/-- Locate a scheduled attempt in the original native run, and recover its
readiness precisely at the memory consulted by its dated record. -/
theorem entryMemory_ready {w q d : ℕ} (C : Chart w q d) (initial : Memory w) (a : Attempt)
    (whole : Calendar.mounted C (events C.mesh) initial) (active : Event.attempt a∈events C.mesh) :
    Calendar.ready C (.attempt a) (entryMemory C initial a) := by
  obtain ⟨i,hi,hit⟩ := List.mem_iff_getElem.mp active
  have pos : position C.mesh (.attempt a)=i := by
    rw [← hit]
    exact position_at C.mesh hi
  have cut:=ordinal_slot C initial ⟨i,hi⟩ whole
  simpa only [entryMemory,pos,hit] using cut.currentReady

/-- The entire low memory interval used by the static subdivision, sign and domain
tables stays intact at the actual dated input, also when a different sector is written. -/
theorem entryMemory_low {w d : ℕ} (chart : Chart w q d) (A : Arena) (start : Memory w) (a : Attempt)
    (mounted : Calendar.mounted chart (events chart.mesh) start)
    (floor : ∀e x,x<A.base chart.mesh e→protected chart x e) (x : ℕ) (low : x<A.first) :
    entryMemory chart start a x=start x := by
  let xs:=events chart.mesh
  let pos:=position chart.mesh (.attempt a)
  have ready := (mounted_append chart (xs.take pos) (xs.drop pos) start).mp
    (by simpa only [List.take_append_drop] using mounted)
  exact run_frame chart _ start x ready.1 (fun e _=>floor e x (low.trans_le (Nat.le_add_right ..)))

omit [Nonempty (Fin k)] in
theorem datedBoard (A : Arena) (chart : Chart bits q D) (m : Memory bits) (a : Attempt)
    (order : Fin R≃Edges s.sampler z (2^W) k) (socket : BoughtSockets.Directory n)
    (seen : CoreRoute.Seen order M groups packed socket depth π m)
    (E : EconomicHeader phases X Y steps) (ord : E.Ordered) (econ : E.Resident m)
    (coreLow : CoreRoute.stop s.sampler z W k n depth G.oldGroups packed.groups G.height R≤A.first)
    (headerLow : E.stop≤A.first) (room : A.first<2^bits)
    (column : G.column=CoreCatalogue.top z W G.oldGroups packed.groups G.height R)
    (names : G.directory.remapBase=CoreCatalogue.groupStart z W)
    (sites : G.directory.sitesBase=CoreCatalogue.siteBase z W G.oldGroups)
    (supers : G.directory.superBase=CoreCatalogue.superStart z W)
    (port : E.ports.header 0=header F (withPorts s c b G) a)
    (mounted : Calendar.mounted chart (events chart.mesh) m)
    (floor : ∀e x,x<A.base chart.mesh e→protected chart x e) :
    DatedBoard F s c b G π groups packed a (entryMemory chart m a) := by
  have preserved:=entryMemory_low chart A m a mounted floor
  have route:=seen.frame (coreLow.trans_lt room) (fun i hi=>preserved i (hi.trans_le coreLow))
  have economic:=EconomicHeader.Resident.move E econ ord (fun i hi=>preserved i (hi.trans_le headerLow))
  refine ⟨?_,route.board.input,?_,port ▸ economic.ports 0⟩
  · rw [column,names,sites,supers]
    exact route.board.columns
  · rw [column]
    exact route.board.rom.keys

end
end Hierarchy.ProtocolRAM.Calendar.StripChart

end OAI
