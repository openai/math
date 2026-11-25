import OAI.Computability.BorderVNP.DiagonalNativeInputAt

/-! # The funded roster on the actual sparse argument visits -/

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

variable {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    {Site : Type}

local notation3 (prettyPrint := false) "R" => a.controlRows team frame offsets ctl live ports
variable (patch : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a f orig data i.val)

/-- Read the roster and the call input from the same funded launch after
identifying the physical memory at the end of fragment generation. -/
theorem SparseEmission.NativeInputAt.rosterOnVisits {description : ℕ}
    (launch : SparseEmission.NativeInputAt id U p e patch row description)
    (atMemory : e.output=(stages).1.val.2.2) :
    ProducedRoster a R (readings (stages).1.val.2.2) patch.placed patch.geometry patch.extra launch.native.source :=
  congrArg (fun mem : Memory w =>
    ProducedRoster a R (readings mem) patch.placed patch.geometry patch.extra launch.native.source) atMemory ▸ launch.roster

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
