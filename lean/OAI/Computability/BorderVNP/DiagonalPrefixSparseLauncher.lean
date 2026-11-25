import OAI.Computability.BorderVNP.DiagonalReachedSparseInputs

/-! # The actual signed sparse task launcher at a returning native prefix -/

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

set_option maxHeartbeats 1600000 in
/-- Submit the padded geometry, immutable typed rows, source segments and
reported bits at the actual argument cut. The very same submission certifies
the source roster used by the per-team clock and the cells inspected at the
final byte of this public preparation. -/
theorem SparseEmission.launched_on_prefix {u v k : ℕ}
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w) (fp : (pub 0).val=frame)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (taskFields : (R).toLayout.Fields raw)
    (ownerOrder : ∀ i, (row i).number.val=idx i.val)
    (rank : ∀ c c' : Fin (R).cells, c<c' → raw ((R).sorted+(R).padded+((R).stops+c.val)) <
      raw ((R).sorted+(R).padded+c'.val))
    (publicEnd : ∀ c < (R).cells, (patch.placed c).publicBase+((patch.placed c).parts.flatMap Part.publicBuffer).length ≤ (R).sorted)
    (geometry : ∀ c < (R).cells, patch.geometry c=(patch.placed c).publicBase+
      ((prefixParts (patch.placed c)).flatMap Part.publicBuffer).length)
    (description : ℕ)
    (originals : ∀ c < (R).cells, ∀ j, Sum.inr j ∈ (patch.placed c).boxes →
      (R).sorted+(R).padded≤(patch.placed c).slot j ∧ (patch.placed c).slot j+description≤a.fragments.external ∧
      (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length≤description)
    (sup : ∀ c < (R).cells, ((patch.extra c).flatMap record).length ≤ (R).stride)
    (stored : ∀ i < num, MergeFields (src i) (R).tasks (R).four i patch.built)
    (sizes : ∀ i < num, ((task) i).cell.payload.length≤a.p.scratchStride ∧ (((task) i).cell.burst w).length≤a.p.burstStride)
    (paid : ∀ c < (R).cells, (R).owner raw c=(R).team →
      (CompactFrame.pack w (Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes)).length ≤ TeamScales.width n (1/2) ∧
      ((logical) c).directory.ProfileWidths ∧ SparseExterior.clock w ((logical) c).directory ((logical) c).privateWires (field c).field ≤ n^25)
    (address : patch.built=(stages).2.1.val.2.2)
    (last : Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac bank patch.built)
    (returned : last.val.2=(visit).arguments.val.2) :
    (∃ data : PinStart.SparseSource id U p, data.logicalAt=logical ∧
      data.bytesAt=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) ∧
      ProducedRoster a R raw patch.placed patch.geometry patch.extra data.source ∧
      data.source.count=num ∧ data.source.owned=os ∧ data.source.tasks=task ∧
      (∀ i : Fin num, data.source.owned i.val=(row i).owned (fit:=fit) (cells:=cells))) ∧
    ∃ out : GeneratedCells SparseExterior.driver n pub p.2.val.2.2, out.cell=logical ∧
      out.payload=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) := by
  obtain ⟨arg,decoded,inputs,bytes,roster,len,owners,tasks,here,runs⟩ :=
    e.signed_call_input mac bank patch row place geo limit fp word controls taskFields ownerOrder rank publicEnd geometry
      description originals sup stored sizes paid
  let saved := fun (m : Memory w) (a : SparseCallInput pub m) =>
    a.count=num ∧ a.owned=os ∧ a.tasks=task ∧ ∀ i : Fin num, a.owned i.val=(row i).owned (fit:=fit) (cells:=cells)
  refine ⟨PinStart.source_of_recorded_launch id U p address arg decoded _ _ inputs bytes a R raw patch.placed patch.geometry
    patch.extra roster saved ⟨len,owners,tasks,here⟩,?_⟩
  obtain ⟨out,localCells,bits,_⟩ := runs last
  have reached := congrArg Prod.snd (returned.trans (PinStart.argument_returned_state id U p))
  rw [←reached]
  exact ⟨out,localCells,bits.trans bytes⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
