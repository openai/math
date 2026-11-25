import OAI.Computability.BorderVNP.DiagonalForwardReachedReportCells

/-! # The actual sparse input and its original reported cells on one prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

variable {teams n w axes b h K symbols : ℕ} (id : TableEntry axes b h K symbols → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix id)
local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "visit" => PinStart.visits id U p
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (visit).reports.val.2.1 (visit).reports.val.2.2).symm (visit).arguments
local notation3 (prettyPrint := false) "bank" => (stages).2.1.val.2.1

variable {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    {Site : Type}

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a f orig data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

set_option maxHeartbeats 2600000 in
set_option maxRecDepth 6000 in
/-- The single input issued by this returned sparse builder. Its logical
graph, transferred bytes and compact ordinals refer to the same actual
pre-call prefix, before any private evaluator acceptance. -/
structure SparseEmission.NativeInputAt (description : ℕ) where
  /-- Selected argument source at the physical call memory. -/
  native : PinStart.SparseSource id U p
  /-- The emitted typed array ends at the actual recorded builder return. -/
  address : patch.built=(stages).2.1.val.2.2
  /-- Verified physical geometry, ordering and payload bounds on this patch. -/
  facts : ReachedReportCells (n:=n) e patch row description
  /-- The compact directory is obtained from the actual cell order. -/
  roster : ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source
  count : native.source.count=num
  owned : native.source.owned=os
  tasks : native.source.tasks=task
  /-- Global logical cell before dispatch compaction. -/
  logicalAt : native.logicalAt=logical
  /-- Packed original bit payload in the emitted sparse directory. -/
  bytesAt : native.bytesAt=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes)
  /-- The private dispatcher materializes the same graph and bytes. -/
  generated : ∃ out : Evaluator.GeneratedCells SparseExterior.driver n pub p.2.val.2.2,
    out.cell=native.logicalAt ∧ out.payload=native.bytesAt

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 6000 in
/-- Read the selected issued source directly from the real producer and its
end address, retaining both the compact and uncompressed representations. -/
noncomputable def SparseEmission.nativeInputAt {u v k description : ℕ}
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w) (fp : (pub 0).val=frame)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (taskFields : (R).toLayout.Fields raw)
    (facts : ReachedReportCells (n:=n) e patch row description) (address : patch.built=(stages).2.1.val.2.2) :
    SparseEmission.NativeInputAt id U p e patch row description := by
  classical
  let selected := e.source_at_reached id U p patch row place geo limit fp word controls taskFields facts address
  let native := selected.choose
  obtain ⟨logicalRows,packedRows,roster,counted,owned,taskRows,_⟩ := selected.choose_spec
  exact ⟨native,address,facts,roster,counted,owned,taskRows,logicalRows,packedRows,native.generated id U⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
