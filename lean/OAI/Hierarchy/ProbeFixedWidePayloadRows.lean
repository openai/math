import OAI.Hierarchy.ProbeFixedWideRowBoards
import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbeFixedPayloadPopulation
import OAI.Hierarchy.ProbeFixedRowGeometry

namespace OAI
/-! # Physical repair geometry at every actual payload ballot of the wide boot -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute StripChart
open StockCommit StripDirectory CatalystArchive BoughtSockets ReportSockets CatalogueRows PurchaseStage
open scoped Fin.CommRing Classical
variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

omit [Nonempty (Fin k)] in
theorem wide_face_room : ∀ᶠ h : ℕ in Filter.atTop,
    let w:=wordBits h (2^v.W) Native.copies
    Fintype.card (Columns h (2^v.W))≤2^w ∧ Stages h (2^v.W)≤2^w ∧ v.sampler.degree≤2^w := by
  let f:=siteFactor (2^v.W) k
  filter_upwards [Filter.eventually_ge_atTop (f+1),Filter.eventually_ge_atTop (publicStages v.W),
    Filter.eventually_ge_atTop v.sampler.degree] with h enough stages degree
  intro w
  have large : h≤2^w:=(Nat.lt_two_pow_self (n:=h)).le.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [w];rw [wordBits_linear];omega))
  have word:=append_room (h:=h) (d:=2^v.W) (copies:=Native.copies) (enough.trans (Nat.lt_two_pow_self (n:=h)).le)
  have columns:=CoreRoute.column_count h (2^v.W) k Nat.one_le_two_pow
  refine ⟨(columns.trans (Nat.le_add_left ..)).trans word.le,?_,degree.trans large⟩
  simpa only [fixed_stage_count] using stages.trans large

variable (h width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.widePlacement h width
local notation "C" => v.nativeChart P h width r banks src tab dst owners
local notation "S" => v.nativeBoards P h width
local notation "E" => v.publicHeader P h width
local notation "A" => v.privateArena P h width
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "order" => v.wideOrder h width
local notation "groups" => WideMemory.groups h v.W
local notation "packed" => WideMemory.dir h v.W k v.wideJobs
local notation "socket" => (v.wideSources h width).2
variable (π : Equiv.Perm (Fin (2^h))) (mem : Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "seen" => CoreRoute.Seen order v.radius groups packed socket v.depth π mem

def wide_payload_rows (boot : seen) («public» : (E).Resident mem) (whole : Calendar.mounted C (events v.mesh) mem)
    (room : (A).endAddress v.mesh<2^W) (catRoom : (P).catalogue.rows<2^W)
    (metric : Public.maxMetric v.radius<2^W) (cols : Fintype.card (Columns h (2^v.W))≤2^W)
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel) :
    v.PayloadRepairGeometry P h width r banks src tab dst owners phase trial (trialState C mem phase trial) := by
  let a:=Attempt.outer phase.val trial.val
  let entry:=trialState C mem phase trial
  let post:=postOutput ((C).layout a) (repair C a) (prepared C a entry)
  have located:=outer_slot C mem phase trial phase.isLt trial.isLt whole
  let tail:=Classical.choose located
  have cut:=Classical.choose_spec located
  have words:=v.wide_row_operands h width r banks src tab dst owners π a entry mem _ tail cut boot «public» room catRoom metric
  refine ⟨words.header,catRoom,order,words.loaded,words.codes,words.fits,?_⟩
  intro row present
  have extent:=cut.currentReady.2.2.2.2.2.1
  change (repair C a).repairBits.base+(v.nativeFormats P h width a).market.rows<2^W at extent
  have atWord:=row.isLt.trans ((Nat.le_add_left ..).trans_lt extent)
  have original:=v.payload_live_lt P h width phase trial ((guard C a).apply entry) row atWord present
  let root : Fin (2^h):=⟨row.val,original⟩
  obtain ⟨col,edges⟩:=v.payload_row_placement_of_fields P h width π groups packed rfl order post
    words.board.columns words.board.input words.loaded cols root (v.date_prefix_fit h).le
  refine ⟨payloadPlace π root,col,?_⟩
  intro e l
  obtain ⟨f,read,metric,_⟩:=edges e l
  exact ⟨f,read,metric⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
