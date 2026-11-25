import OAI.Computability.BorderVNP.DiagonalFrozenPostReportWords
import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.RoutingISASignedPrepReports
import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost

/-! # The issued report frame on the original frozen signed publisher -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally ScheduleClock Packing GeometryAdvice
open TeamContraction TeamContraction.ProcessorSlots DiagonalTallyAllocation DiagonalTallyCellReports

variable {w R n : ℕ} (a : SignedTaskArena.Layout) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (u : Fin (R+1)) (active : (U u).Prefix a.id) {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {pins : Pins.Layout} {slotted : Memory w} {next : ℕ}
    {I : Type*} [Fintype I] {host : I → Fin a.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    (slot : SlottedWriter a.cube dir pp lp pins (U u).pub slotted next host key sizes)
    {head : ℕ} (atHead : head=readings (U u).pub 0)
    {frame : BroadcastFrame} {old : Fin 81 → Word w} {gates bits off ell tail depth : ℕ}
    {history : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast a.cube.n a.cube.header.d a.cube.header.cap}
    {X : ℕ}

local notation3 (prettyPrint := false) "pub" => (U u).pub
local notation3 (prettyPrint := false) "vr" => visits a.id U active
local notation3 (prettyPrint := false) "fresh" => next+7*dir.candidates
local notation3 (prettyPrint := false) "live" => dir.teams*dir.sites
local notation3 (prettyPrint := false) "ordinary" => PackedHistoryCircuit.TerminalCells.signedGridOutputCount
  a.cube.cables a.cube.cells dir.entries live 37 tail
local notation3 (prettyPrint := false) "words" => ordinary+(2^depth+2^depth)
local notation3 (prettyPrint := false) "dest" => Allocation.dest fresh history.length gates words bits
local notation3 (prettyPrint := false) "ctl" => RoutingOutputs.controlsBase dest a.cube.cables a.cube.cells dir.entries live
local notation3 (prettyPrint := false) "offsets" => (RoutingOutputs.bases dest a.cube.cables a.cube.cells dir.entries).ends
local notation3 (prettyPrint := false) "rows" => (dir.directory pp lp).length
local notation3 (prettyPrint := false) "installed" => Directory.ISA.publish slotted head next (dir.directory pp lp)

set_option maxRecDepth 6500
set_option maxHeartbeats 1800000

include atHead slot in
/-- Apply the arbitrary-prefix opening on the same publisher that ran at
this team. The frozen packet includes the two marked banks after its
ordinary sections. Its native slot pointer, size and endpoints all come
from the returned source before the report was guessed. -/
theorem issued_from_pinned_writer
    (room : SignedPrep.PinnedRawInput (ar:=a.cube) (D:=dir) (pp:=pp) (lp:=lp) («pub»:=pub)
      (slotted:=slotted) (base:=next) frame old fresh gates words bits off ell ctl history claims pad raw R X)
    {inputs guesses readerGates : ℕ} (endFits : a.endAddress w inputs guesses readerGates < 2^w)
    {L : ReportLayout} {cs : List (ReportCell L)} {cur : ReportCursor} {description : ℕ} {bl : CellBanks.Layout}
    (seed : PreparedReportInput pub (vr).controls.val.2.2 cs cur description)
    (alloc : ReportAllocation a.before a.after bl L cs cur) (bank : bl.bankStart=a.cube.cellBank)
    (opening : ∀ prof gateBound outputs outWidth suffix query guess read : ℕ,
      dest=Allocation.dest fresh prof gateBound outputs outWidth →
      a.cube.header.header=Allocation.stop fresh prof gateBound outputs outWidth w →
      PackedHistoryCircuit.TerminalCells.signedGridOutputCount a.cube.cables a.cube.cells dir.entries live 37 suffix ≤ outputs →
      a.endAddress w query guess read < 2^w → readings slotted (head+8)=next →
      rows+a.cube.header.d.choose 2 ≤ a.cube.maxRows →
      LabelIndex.Endpoints (LabelIndex.layout head (readings installed)) (readings installed) →
      ∀ {b : CellBanks.Layout} {l : ReportLayout} {cells : List (ReportCell l)} {cursor : ReportCursor} {desc : ℕ},
        PreparedReportInput pub (vr).controls.val.2.2 cells cursor desc →
        ReportAllocation a.before a.after b l cells cursor → b.bankStart=a.cube.cellBank →
        IssuedReportFrame a pub (vr).reports.val.2.2 offsets ctl rows) :
    IssuedReportFrame a pub (vr).reports.val.2.2 offsets ctl rows ∧ rows ≤ a.cube.maxRows := by
  have count : rows+a.cube.header.d.choose 2 ≤ a.cube.maxRows := room.records
  refine ⟨?_,(Nat.le_add_right ..).trans count⟩
  apply opening history.length gates words bits tail inputs guesses readerGates rfl
    (congrArg CubeHeaderInstall.Inputs.header room.geometry) (Nat.le_add_right ..) endFits _ count _ seed alloc bank
  · rw [atHead]
    exact slot.pointers.1
  · rw [atHead]
    exact room.labels.endpoints

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
