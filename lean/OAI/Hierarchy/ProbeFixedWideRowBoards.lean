import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProbeFixedPrintedOperands
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueGeometry

namespace OAI
/-! # Physical readback of the wide catalogue at the priced output of each true event -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (h width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "E" => v.publicHeader P h width
local notation "A" => v.privateArena P h width
local notation "G" => v.stamp P h width r banks src tab dst owners
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "b" => (P).catalogue
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "coreEnd" => CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth
  (WideMemory.K h v.W) (packed).groups (WideMemory.H h v.W k v.wideJobs) (b).coreRows
local notation "bh" => StripChart.header F S
variable (π : Equiv.Perm (Fin (2^h)))
local notation "seen[" m "]" => CoreRoute.Seen order v.radius groups packed socket v.depth π m
variable (a : Attempt) (entry : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "post" => postOutput ((C).layout a) (repair C a) (prepared C a entry)

structure WideRowOperands : Prop where
  board : DatedBoard F S v.mesh b (P).routes π groups packed a post
  observed : seen[post]
  loaded : CoreLookup.Loaded (P).routes.core order post
  codes : ∀f,(b).core.lengthCode.eval post (((order).symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W)
  header : (bh a).stop≤(G a).out
  room : (b).rows<2^W
  fits : ∀f : Edges v.sampler h (2^v.W) k,coreCode v.sampler v.radius f<2^W

omit [Nonempty (Fin k)] in
/-- The physical catalogue uses the length field of its installed core-row source. -/
theorem wide_row_code_field :
    (b).core.lengthCode =
      (CoreCatalogue.sourceAt h v.W k v.wideJobs (b).coreRows (WideMemory.K h v.W)
        (packed).groups (WideMemory.H h v.W k v.wideJobs) (CoreCatalogue.pointBits h v.W)).lengthCode := by
  rfl

omit [Nonempty (Fin k)] in
theorem wide_row_operands (init : Memory W) (prior tail : List Event)
    (cut : Slot C init (.attempt a) prior tail entry) (seen : seen[init]) («public» : (E).Resident init)
    (endRoom : (A).endAddress v.mesh<2^W) (catRoom : (b).rows<2^W) (metric : Public.maxMetric v.radius<2^W) :
    v.WideRowOperands h width r banks src tab dst owners π a entry := by
  have early (x : ℕ) (hx : x<(A).first) : post x=init x := by
    have low (e : Event) : x<(A).base v.mesh e:=hx.trans_le (Nat.le_add_right ..)
    have protect (e : Event) := (v.event_prefix P h width r banks src tab dst owners e x (low e)).1
    have step:=postOutput_prior C a entry x cut.currentReady (protect (.attempt a))
    have prev : entry x=init x:=by
      rw [←cut.entry]
      exact run_frame C _ _ _ cut.prefixReady (fun e _=>protect e)
    exact step.trans prev
  have arenaWord : (A).first<2^W := (Nat.le_add_right ..).trans_lt endRoom
  have coreLow : coreEnd≤(A).first :=
    (v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have snap : seen[post]:=seen.frame (coreLow.trans_lt arenaWord) (fun i hi=>early i (hi.trans_le coreLow))
  have ord : (E).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh
    (P).joint b (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have eLow : (E).stop≤(A).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)
  have pub:=EconomicHeader.Resident.move E «public» ord (fun x hx=>early x (hx.trans_le eLow))
  have ports : (E).ports.header 0=bh a := by
    cases a <;> simp only [PortROM.Table.header,Fin.val_zero,Nat.zero_mul,Nat.add_zero] <;> rfl
  have board : DatedBoard F S v.mesh b (P).routes π groups packed a post :=
    ⟨snap.board.columns,snap.board.input,snap.board.rom.keys,(v.catalyst_header P h width a) ▸ pub.ports 0⟩
  have codes (f : Edges v.sampler h (2^v.W) k) := (snap.board.rows ((order).symm f)).2.2.2.1
  refine ⟨board,snap,snap.lookup,?_,?_,catRoom,fun f=>(Public.coreCode_le _ _ f).trans_lt metric⟩
  · intro f
    rw [v.wide_row_code_field h width]
    simpa only [(order).apply_symm_apply] using codes f
  · rw [←ports]
    exact ((E).ports.end_le 0).trans ((v.catalyst_ports_le_first P h width).trans
      ((Nat.le_add_right ..).trans (v.stock_label P h width a)))

omit [Nonempty (Fin k)] in
/-- Catalogue row counts scale linearly in the population; its fixed public
edge metric fits simultaneously for every permissible placement width. -/
theorem wide_row_room : ∀ᶠ h : ℕ in Filter.atTop,∀width : ℕ,
    (v.widePlacement h width).catalogue.rows<2^(Native.wordBits h (2^v.W) Native.copies) ∧
    Public.maxMetric v.radius<2^(Native.wordBits h (2^v.W) Native.copies) := by
  filter_upwards [Filter.eventually_ge_atTop (v.rowFactor+1),Public.metric_eventually v.W v.radius] with h big small
  intro width
  have enough : v.rowFactor+1≤2^h:=big.trans (Nat.lt_two_pow_self (n:=h)).le
  have tall:=append_room (h:=h) (d:=2^v.W) (copies:=Native.copies) enough
  exact ⟨((v.wideCatalogueRows h width).trans (Nat.le_add_left ..)).trans_lt tall,small⟩


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
