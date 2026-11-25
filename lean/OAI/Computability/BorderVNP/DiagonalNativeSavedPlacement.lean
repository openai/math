import OAI.Computability.BorderVNP.DiagonalNativeInputAt
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands

/-! # Retaining the same sparse source's public placement on a booted calendar -/

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

open CellPacketGeometry CellPacketGeometry.SiteWords CellPacketGeometry.History.Native

/-- Reveal the original returned geometric shape, added records, and field of
the exact launched native source. These are held for the original cell-bank
readback, on the same emitter used to certify each owned private call. -/
theorem SparseEmission.NativeInputAt.savedPlacement {description tags cellsN : ℕ}
    {directory : BorderVNP.CellPacketGeometry.SiteWords.Directory (Fin tags) Site (cellsN+1)} (launch : SparseEmission.NativeInputAt id U p e patch row description)
    (shape : ∃ pl : Fin (cellsN+1) → Placed Site, TypedBatch.SourceShape pl directory ∧ patch.placed=BorderVNP.CellPacketGeometry.History.Native.Terminal.placeAt pl) :
    ∃ (pl : Fin (cellsN+1) → Placed Site) (extra : ℕ → List Record) (view : ℕ → SparseExterior.Field),
      TypedBatch.SourceShape pl directory ∧ launch.native.logicalAt =
        fun c => SparseExterior.logicalCell (BorderVNP.CellPacketGeometry.History.Native.Terminal.placeAt pl c) (extra c) (view c) := by
  obtain ⟨pl,emitted,atOrdinal⟩ := shape
  refine ⟨pl,patch.extra,fun c => (field c).field,emitted,?_⟩
  rw [←atOrdinal]
  exact launch.logicalAt

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
