import OAI.Computability.BorderVNP.DiagonalReachedReportCells
import OAI.Computability.BorderVNP.DiagonalPrefixSparseLauncher

/-! # The sparse source on a returning jointly prepared team -/

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

set_option maxHeartbeats 1200000 in
/-- Transfer the authentic row, report bank and ownership record from the actual
typed construction into the private generator on the same prefix. -/
theorem SparseEmission.source_at_reached {u v k description : ℕ}
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w) (fp : (pub 0).val=frame)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (taskFields : (R).toLayout.Fields raw)
    (facts : ReachedReportCells (n:=n) e patch row description) (address : patch.built=(stages).2.1.val.2.2) :
    ∃ native : PinStart.SparseSource id U p, native.logicalAt=logical ∧
      native.bytesAt=(fun c => Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes) ∧
      ProducedRoster a R raw patch.placed patch.geometry patch.extra native.source ∧
      native.source.count=num ∧ native.source.owned=os ∧ native.source.tasks=task ∧
      (∀ i : Fin num, native.source.owned i.val=(row i).owned (fit:=fit) (cells:=cells)) := by
  obtain ⟨arg,decoded,inputs,bytes,roster,len,owners,tasks,here,_⟩ :=
    e.signed_call_input mac bank patch row place geo limit fp word controls taskFields facts.ownerOrder facts.rank
      facts.publicEnd facts.geometry description facts.originals facts.sup facts.stored facts.sizes facts.paid
  let saved := fun (m : Memory w) (a : SparseCallInput pub m) =>
    a.count=num ∧ a.owned=os ∧ a.tasks=task ∧ ∀ i : Fin num, a.owned i.val=(row i).owned (fit:=fit) (cells:=cells)
  exact PinStart.source_of_recorded_launch id U p address arg decoded _ _ inputs bytes a R raw patch.placed patch.geometry
    patch.extra roster saved ⟨len,owners,tasks,here⟩

end RoutingISA.FragmentRows

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM BorderVNP.Cube ScheduleClock SignedTaskArena FragmentRows CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

variable {T n w dim b h K symbols : ℕ} (id : TableEntry dim b h K symbols → ℕ)
    (U : Fin (T+1) → PinStart SparseExterior.driver n w) {u : Fin (T+1)} (p : (U u).Prefix id)
    (a : SignedTaskArena.Layout) {qin qgu qg team offsets ctl live ports : ℕ} {Site : Type}
local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U u).routines
local notation3 (prettyPrint := false) "V" => visits id U p
local notation3 (prettyPrint := false) "s" => (V).reports.val.2.1
local notation3 (prettyPrint := false) "m" => (V).reports.val.2.2
local notation3 (prettyPrint := false) "mem" => readings m
local notation3 (prettyPrint := false) "head" => readings pub 0
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head mem
local notation3 (prettyPrint := false) "R" => a.controlRows team head offsets ctl live ports
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac s m).symm (V).arguments

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3200000 in
/-- The forward source and roster use exactly the emitter, compact typed return and rows
that construct the bare report inverse. The check applies before any private-cell result. -/
theorem source_of_reached_reports (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (geo : SparseGeometry a f offsets ctl)
    (cables : (f).host.count=a.cube.cables) (raw : mem (head+9)≤a.cube.maxRows)
    (cellCount : mem (head+11)=a.cube.cells) (high : a.endAddress w qin qgu qg<2^w)
    (outer : (R).Fields mem) (word : mem (head+30)=w)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(a.tasks team head offsets ctl).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team)) (description : ℕ)
    (saved : (e : SparseEmission a f m fit cellCount.symm) → SparsePatch (w:=w) Site (R) (readings e.output) →
      (data : ℕ → ℕ → Bool) → ((i : Fin ((R).before (readings e.output) (R).cells)) → SparseCell a f m data i.val) → Prop)
    (reached : ∀ (first : Returns emitBucket pub mac s m) (e : SparseEmission a f m fit cellCount.symm),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ∀ next : Returns TypedTaskBuilder.program pub mac e.bank e.output,
        readings next.val.2.2=(R).toLayout.published (readings e.output) →
        ∃ patch : SparsePatch (w:=w) Site (R) (readings e.output), patch.built=next.val.2.2 ∧
          ∃ (data : ℕ → ℕ → Bool) (row : (i : Fin ((R).before (readings e.output) (R).cells)) →
            SparseCell a f m data i.val), ReachedReportCells (n:=n) e patch row description ∧ saved e patch data row) :
    ∃ (e : SparseEmission a f m fit cellCount.symm), e.bank=(parts).1.val.2.1 ∧ e.output=(parts).1.val.2.2 ∧
      ∃ patch : SparsePatch (w:=w) Site (R) (readings e.output), patch.built=(parts).2.1.val.2.2 ∧
      ∃ (data : ℕ → ℕ → Bool) (row : (i : Fin ((R).before (readings e.output) (R).cells)) →
          SparseCell a f m data i.val) (native : SparseSource id U p),
        let field := e.globalCells (team:=team) (frame:=head) (offsets:=offsets) (ctl:=ctl) (live:=live) (ports:=ports) row
        let ordinal := globalCell (R).toLayout (readings e.output)
        let inputs := Batch.produced (R) (readings e.output) patch.placed patch.geometry patch.extra
        let layout := batchLayout a head ctl ((R).before (readings e.output) (R).cells)
        let logical := fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field
        ReachedReportCells (n:=n) e patch row description ∧ saved e patch data row ∧ native.logicalAt=logical ∧
        native.bytesAt=(fun c => Packet.input (logical c).directory (logical c).privateWires (field c).field.bytes) ∧
        ProducedRoster a (R) (readings e.output) patch.placed patch.geometry patch.extra native.source ∧
        native.source.count=(R).before (readings e.output) (R).cells ∧
        native.source.owned=(fun i => field (ordinal i)) ∧
        native.source.tasks=(fun i => (field (ordinal i)).typed layout (inputs i).typed) ∧
        (∀ i, native.source.owned i.val=(row i).owned (fit:=fit) (cells:=cellCount.symm)) := by
  have order := a.sparse_order place.cells
  have low := place.beforeBank.trans (order.1.trans order.2.1)
  obtain ⟨e,hb,hm⟩ := emission_of_return pub mac s m a fit ptr words place.beforeControl low cables raw cellCount high
    (parts).1.property
  let next : Returns TypedTaskBuilder.program pub mac e.bank e.output :=
    ⟨(parts).2.1.val,by simpa only [hb,hm] using (parts).2.1.property⟩
  have fields := e.task_fields ptr place outer calls tasks words
  have room := e.task_room_owned (team:=team) ptr place geometry high
  obtain ⟨_,_,_,typed,_,image⟩ := TypedTaskBuilder.program_run pub mac e.bank e.output (R).toLayout rfl fields room
  have imageAt := (congrArg readings (next.property.unique_of_deterministic (by decide) typed).2.2).trans image
  obtain ⟨patch,built,data,row,facts,tracked⟩ := reached (parts).1 e hb hm next imageAt
  obtain ⟨native,logical,bytes,roster,count,owners,taskRows,owned⟩ := SparseEmission.source_at_reached id U p e patch row
    place geo high rfl word words fields facts built
  exact ⟨e,hb,hm,patch,built,data,row,native,facts,tracked,logical,bytes,roster,count,owners,taskRows,owned⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
