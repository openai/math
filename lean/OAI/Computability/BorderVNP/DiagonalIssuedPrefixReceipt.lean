import OAI.Computability.BorderVNP.DiagonalEmittedPrefixOwner
import OAI.Computability.BorderVNP.DiagonalNativeInputAt

/-! # Acquire the selected sparse input and its owner table from the same patch -/

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


open CellMacro.Generator CompactMachine

/-- Acquire one native sparse input with its true owner column and the returned
logical values. The packet and its retained placement have exactly the same
compiler witness in the result as on the original native prefix. -/
theorem issuedPrefixReceipt {who : Fin a.cube.cells → Fin (T+1)} (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^bound) w)
    (position : OpenSuffix.Placement (a.openInputs team head offsets ctl live ports bundles bound home headers)
      a.cube a.before head (readings (V).owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs team head offsets ctl live ports bundles bound home headers) head
      (readings (V).owned.val.2.2) w)
    {description : ℕ} (seed : PreparedReportInput pub (V).controls.val.2.2 cs cursor description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs cursor)
    {fit : (f).Fits w mem} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f m fit cells) (ptr : mem (head+92)=ctl) (banked : e.output=(parts).1.val.2.2)

    {data : ℕ → ℕ → Bool}
    (rows : (i : Fin ((R).toLayout.before (readings e.output) a.cube.cells)) → SparseCell a f m data i.val)
    (source : ∀ c : Fin a.cube.cells, readings (V).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=(who c).val)
    {I : Type} (index : I → ℕ) (want : I → CellInput)
    (saved : (patch : SparsePatch (w:=w) Site (R) (readings e.output)) →
      SparseEmission.NativeInputAt id U p e patch rows description → Prop)
    (packet : ∃ patch, ∃ launch : SparseEmission.NativeInputAt id U p e patch rows description,
      saved patch launch ∧ ∀ i, launch.native.logicalAt (index i)=want i) :
    ∃ native : SparseSource id U p,
      OwnerTable pub p.2.val.2.2 ⟨team,a.before.limit,a.cube.cells⟩ (PositiveTeam.ownerWord who) ∧
      (∀ i, native.logicalAt (index i)=want i) ∧
      Nonempty {evidence : (patch : SparsePatch (w:=w) Site (R) (readings e.output)) ×
        SparseEmission.NativeInputAt id U p e patch rows description //
        evidence.2.native=native ∧ saved evidence.1 evidence.2} := by
  obtain ⟨patch,launch,geometry,exactCell⟩ := packet
  refine ⟨launch.native,?_,exactCell,⟨⟨⟨patch,launch⟩,rfl,geometry⟩⟩⟩
  exact ownerTable_at_prefix a id U p home headers axis room position ready seed alloc e ptr banked
    patch.placed patch.geometry patch.extra launch.native launch.roster source

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
