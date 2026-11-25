import OAI.Computability.BorderVNP.DiagonalEmittedOwnerTable
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow

/-! # The complete sparse owner table on the original native prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open CellDispatch FiniteEvaluator DiagonalTallyCellReports SignedPrep TeamContraction
open VPVNP.BurstRAM BorderVNP.Cube ScheduleClock SignedTaskArena FragmentRows CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

variable {T n w : ℕ} (a : SignedTaskArena.Layout)
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (T+1) → PinStart SparseExterior.driver n w) {u : Fin (T+1)} (p : (U u).Prefix id)
    {qin qgu qg team offsets ctl live ports bundles bound : ℕ} {Site : Type}
    (home : Fin bundles → Fin a.cube.cells) (headers : Fin bundles → Packing.BottomReports.BundleHeader)
    {l : ReportLayout} {cursor : ReportCursor} {cs : List (ReportCell l)}
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

/-- Keep the real sparse task source fixed while transporting all its owners through the native
argument return of this very prefix. -/
theorem ownerTable_at_prefix {who : Fin a.cube.cells → Fin (T+1)} (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^bound) w)
    (position : OpenSuffix.Placement (a.openInputs team head offsets ctl live ports bundles bound home headers)
      a.cube a.before head (readings (V).owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs team head offsets ctl live ports bundles bound home headers) head
      (readings (V).owned.val.2.2) w)
    {description : ℕ} (seed : PreparedReportInput pub (V).controls.val.2.2 cs cursor description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs cursor)
    {fit : (f).Fits w mem} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f m fit cells) (ptr : mem (head+92)=ctl) (banked : e.output=(parts).1.val.2.2)
    (placed : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (native : SparseSource id U p) (produced : ProducedRoster a (R) (readings e.output) placed geom extra native.source)
    (source : ∀ c : Fin a.cube.cells, readings (V).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=(who c).val) :
    OwnerTable pub p.2.val.2.2 ⟨team,a.before.limit,a.cube.cells⟩ (PositiveTeam.ownerWord who) := by
  have table := (V).ownerTable_after_emission a home headers who axis room position ready seed alloc e ptr source
    placed geom extra banked native.source produced
  simpa only [visits,Equiv.apply_symm_apply] using table

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
