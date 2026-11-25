import OAI.Hierarchy.ProbeFixedWidePayloadRows
import OAI.Hierarchy.ProbeFixedWideBirthRows
import OAI.Hierarchy.ProbeFixedPurchasedRowWitness

namespace OAI
/-! # Purchased repair coordinates at every bounded inner date of the original wide run -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage PurchaseFrozen
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (h width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "E" => v.publicHeader P h width
local notation "A" => v.privateArena P h width
local notation "N" => Stages h (2^v.W)
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
local notation "coreEnd" => CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth
  (WideMemory.K h v.W) (packed).groups (WideMemory.H h v.W k v.wideJobs) (P).catalogue.coreRows
local notation "keyPage" => Public.keyHead v.sampler (P).routes.column h v.W k v.depth
variable (π : Equiv.Perm (Fin (2^h))) (mem : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "seen" => CoreRoute.Seen order v.radius groups packed socket v.depth π mem

set_option maxHeartbeats 2000000 in
def wide_purchased_rows (boot : seen) («public» : (E).Resident mem) (whole : Calendar.mounted C (events v.mesh) mem)
    (room : (A).endAddress v.mesh<2^W) (catRoom : (P).catalogue.rows<2^W)
    (metric : Public.maxMetric v.radius<2^W) (cols : Fintype.card (Columns h (2^v.W))≤2^W)
    (stages : N≤2^W) (degree : v.sampler.degree≤2^W) (late : v.stripHeight≤h)
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice : Fin v.mesh.reserveSteps) (inner : Fin v.mesh.innerFuel) :
    v.PurchasedRepairGeometry P h width r banks src tab dst owners phase trial slice inner
      (innerState C mem phase trial slice inner) := by
  let a:=Attempt.inner phase.val trial.val slice.val inner.val
  let entry:=innerState C mem phase trial slice inner
  let post:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
  have slot := inner_slot C mem phase trial slice inner phase.isLt trial.isLt slice.isLt inner.isLt whole
  let tail := Classical.choose slot
  have cut := Classical.choose_spec slot
  have words:=v.wide_row_operands h width r banks src tab dst owners π a entry mem _ tail cut boot «public» room catRoom metric
  have born:=v.wide_birth_rows h width r banks src tab dst owners π mem boot whole room phase trial slice inner
  have cap : ((P).routes.directory.header h (2^v.W) k v.sampler.degree v.depth).count≤(P).catalogue.boughtRows:=le_rfl
  have sourcePrefix:=v.wideGeometryPrefix h width
  have first:=v.catalyst_initial_le_first P h width
  have low : (keyPage).stop≤(A).first := (show (keyPage).stop≤coreEnd from
    (Public.borders v.sampler (P).routes.column h v.W k v.wideJobs v.depth).2.trans (Nat.le_add_right ..)).trans
      (sourcePrefix.2.2.trans first)
  have orig : Shelf.Geometry π mem:=fun i=>⟨_,boot.board.columns.geometry i⟩
  have cells:=v.purchased_table_room h late
  refine ⟨words.header,catRoom,order,words.loaded,words.codes,words.fits,?_⟩
  intro row active
  obtain ⟨marks,unique,path,ordinal,records⟩:=v.purchased_post_path P h width r banks src tab dst owners mem π
    phase trial slice inner whole orig (sourcePrefix.2.1.trans first) low boot.board.rom.keys born late row active
  obtain ⟨col,edges,last⟩:=v.purchased_row_placement_of_fields P h width π groups packed rfl rfl order post
    phase trial words.board.columns words.board.strata words.loaded cols marks unique path records
    cells.1 cells.2.1 stages degree (v.date_prefix_fit h).le cap catRoom
  rw [← ordinal]
  refine ⟨retainedCol π marks path,col,?_,last⟩
  intro e l
  obtain ⟨f,read,length,_⟩:=edges e l
  exact ⟨f,read,length⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
