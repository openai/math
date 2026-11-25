import OAI.Hierarchy.ProbeFixedForestCheckout
import OAI.Hierarchy.ProbeFixedWideRowBoards
import OAI.Hierarchy.ProbeFixedPrintedOperands
import OAI.Hierarchy.ProbeFixedGuardPages
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueGeometry

namespace OAI
/-! # Permanent physical row operands after all clock events -/

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

structure WideForestBase (m : Memory W) : Prop where
  board : ∀a,DatedBoard F S v.mesh b (P).routes π groups packed a m
  observed : seen[m]
  loaded : CoreLookup.Loaded (P).routes.core order m
  catalogue : ∀f,(b).core.lengthCode.eval m (((order).symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W)
  «public» : (E).Resident m

omit [Nonempty (Fin k)] in
theorem wide_forest_base {init final : Memory W} (seen : seen[init]) («public» : (E).Resident init)
    (endRoom : (A).endAddress v.mesh<2^W) (early : ∀x : ℕ,x<(A).first→final x=init x) :
    v.WideForestBase h width π final := by
  have arenaWord : (A).first<2^W := (Nat.le_add_right ..).trans_lt endRoom
  have coreLow : coreEnd≤(A).first :=
    (v.wideGeometryPrefix h width).2.2.trans (v.catalyst_initial_le_first P h width)
  have snap : seen[final]:=seen.frame (coreLow.trans_lt arenaWord) (fun i hi=>early i (hi.trans_le coreLow))
  have ord : (E).Ordered:=economic_ordered F (v.sized (v.seed P h width) width) v.cost v.mesh
    (P).joint b (P).routes v.finish (v.basePhase width) v.digitRadix v.digitRadix v.precision v.precision
  have eLow : (E).stop≤(A).first := (Nat.le_add_right ..).trans (v.header_scoreEnd_le_first P h width)
  have pub:=EconomicHeader.Resident.move E «public» ord (fun x hx=>early x (hx.trans_le eLow))
  have board (a : Attempt) : DatedBoard F S v.mesh b (P).routes π groups packed a final :=
    ⟨snap.board.columns,snap.board.input,snap.board.rom.keys,(v.catalyst_header P h width a) ▸ pub.ports 0⟩
  refine ⟨board,snap,snap.lookup,?_,pub⟩
  intro f
  rw [v.wide_row_code_field h width]
  simpa only [(order).apply_symm_apply] using (snap.board.rows ((order).symm f)).2.2.2.1

omit [Nonempty (Fin k)] in
theorem wide_forest_run_base (m : Memory W) (boot : seen[m]) («public» : (E).Resident m)
    (endRoom : (A).endAddress v.mesh<2^W) (full : Calendar.mounted C (events v.mesh) m) :
    v.WideForestBase h width π (run C (events v.mesh) m) := by
  apply v.wide_forest_base h width π boot «public» endRoom
  intro x low
  apply run_frame C _ _ _ full
  intro e _
  exact (v.event_prefix P h width r banks src tab dst owners e x (low.trans_le (Nat.le_add_right ..))).1

omit [Nonempty (Fin k)] in
theorem wide_forest_checkout_base (flag : ℕ) (m : Memory W) (boot : seen[m]) («public» : (E).Resident m)
    (endRoom : (A).endAddress v.mesh<2^W) (full : Calendar.mounted C (events v.mesh) m) (after : (A).first≤flag) :
    v.WideForestBase h width π (checkedOut C flag m) :=
  v.wide_forest_base h width π boot «public» endRoom
    (v.paid_forest_checkout P h width r banks src tab dst owners flag m full after)


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
