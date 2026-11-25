import OAI.Computability.BorderVNP.DiagonalReturnedWriterReportFrame
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership
import OAI.Computability.BorderVNP.DiagonalJointWriterHost

/-! # The physical original writer and report frame of one issued prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP VPVNP.BurstRAM FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyRAM DiagonalTallyMaterialize BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Physical
open BorderVNP.Cube.Padding.Banks TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open TeamContraction.JointHeader.PositiveFields ScheduleClock Crossing TeamScales CellPacketGeometry
open RoutingISA.Transmission RoutingISA.CompactMachine CellMacro.Generator Diagonal.Layout
open Diagonal.ExternalSew.Fragments Routing Cube.Scatter Cube.TeamRows Cube.Scatter.Assignment
open DiagonalTallyPacketEmit SignedTaskArena
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 3200000
set_option maxRecDepth 6500

variable {w R n : ℕ} (a : SignedTaskArena.Layout) (U : Fin (R+1) → PinStart SparseExterior.driver n w)
    (active : JointPrefix a.id U) (teamSlot : Fin (R+1))
    (offsets ctl live ports : ℕ)
local notation3 (prettyPrint := false) "pub" => (U teamSlot).pub
local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (U teamSlot).routines
local notation3 (prettyPrint := false) "V" => visits a.id U (active teamSlot)

variable {r sites pins link inner : ℕ} {Edge : Type} {G : Wiring R r sites pins link inner n Edge}
    {livePin : Fin pins → Bool} {wire : WireLayout (R+1) r link} {common : List Bool}
    {publicAt : HeaderExterior wire common → Fin (R+1) → Arg → Word w}
    {macroAt : HeaderExterior wire common → Fin (R+1) → TeamOpcode.Macros w 8}
    {regsAt : HeaderExterior wire common → Fin (R+1) → Bank w}
    {memoryAt : HeaderExterior wire common → Fin (R+1) → Memory w}
    {decl : LengthDeclaration a.cube.n a.cube.header.d}
    (F : PreparationFrame G wire a.cube decl common livePin publicAt macroAt regsAt memoryAt)
    (seen : HeaderExterior wire common) (ext : Exterior R r link → Bool)
    {owners : (Packet a.cube.n a.cube.header.d a.cube.header.blocks →
      Selector a.cube.n a.cube.K a.cube.h) → Fin a.cube.header.d → Fin (R+1)}
    {template : DiagonalTallyPacketEmit.Frame} {rows : ℕ} (route : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) owners)
    (atOwned : F.ReturnedOwnershipAt a seen ext template rows route (ownedVisits (ar:=a.cube) U active))


variable {writerReg writerEnd : Bank w} {entered after : Memory w} {events : List (TeamRAM.Event w)}
    (W : WriterHistory a.cube.n (Tally.selectorWidth a.cube.n a.cube.K a.cube.h) (U teamSlot).pub
      (install SparseExterior.driver n (U teamSlot).routines) writerReg entered events writerEnd after)
    (done : ReturnedWriters a.cube F.dataDir F.privatePlacement F.livePlacement F.cellOwner decl F.group
      (G.pinLayout teamSlot (F.inputBase teamSlot) (F.columnBase teamSlot) (F.referenceBase teamSlot)) W)
    (source : F.source seen teamSlot=readings W.sharedInput)

include atOwned done source in
/-- A reached owned scan retains the physical words of its own published
writer. Both sides name the same returned origin even when the selected
preparation uses a different index for it. -/
theorem issued_writer_host :
    CubeAllocation.HostRetention a.cube (pub 0).val (readings entered) (readings W.dataInput)
      (readings (V).owned.val.2.2) := by
  obtain ⟨H,f,writer,_,handoff,observed⟩ := atOwned
  have pubEq : pub=(H teamSlot).pub := handoff.pub teamSlot
  have primary : (pub 0).val+112 ≤ a.cube.header.header := by
    rw [pubEq]
    exact (handoff.room teamSlot).primary
  have frame : F.rows.frame=(pub 0).val :=
    (handoff.frame teamSlot).trans (congrFun (congrArg readings pubEq) 0).symm
  have retained (j : ℕ) (hj : j<a.cube.records)
      (extent : j<a.cube.header.header+13 ∨ a.cube.publicBase≤j)
      (n13 : j≠(pub 0).val+13) (n46 : j≠(pub 0).val+46) :
      readings (V).owned.val.2.2 j=readings W.dataInput j := by
    have kept := writer.owned_output_static (F.frame seen) handoff observed teamSlot j hj extent (frame ▸ n13) n46
    have low : W.sharedInput j=W.dataInput j := by
      rw [W.dataImage done.emission.demand.ready,DataWriter.publish,Function.update_of_ne n13,
        Packing.Directory.ISA.putWords_outside _ _ _ _ (.inl (done.emission.demand.records ▸ hj))]
    exact kept.trans ((congrFun source j).trans (congrArg Fin.val low))
  obtain ⟨_,_,_,_,_,_,_,_⟩ := a.cube.writer_order
  refine ⟨primary,fun j hj n13 n46 => (retained j (by omega) (.inl (by omega)) n13 n46).trans
    (congrArg Fin.val (done.low j hj)),?_⟩
  intro j lo hi
  exact retained j hi (.inr lo) (by omega) (by omega)

local notation3 (prettyPrint := false) "rep" => (V).reports.val.2.2
local notation3 (prettyPrint := false) "frag" => FragmentRows.Layout.fromFrame (pub 0).val (readings rep)

include atOwned done source in
/-- The original arbitrary issued prefix recovers its full fragment frame,
including the precise length of its own preparation frame's routed input
directory. The report may contain any submitted bits. -/
theorem issued_writer_report_frame
    {fit : (FragmentRows.Layout.fromFrame (pub 0).val (readings rep)).Fits w (readings rep)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame (pub 0).val (readings rep)).cells}
    (e : FragmentRows.SparseEmission a frag rep fit cells)
    (A : StartupArena) {reserve axes groups cap width query guesses gates : ℕ}
    (addresses : a.FinishAddresses A ctl reserve axes groups cap width w query guesses gates)
    (atFrame : (pub 0).val=A.frame) (geometry : FragmentRows.SparseGeometry a frag offsets ctl)
    (controls : ∀ i : Fin 37, readings rep (ctl+i.val)=a.controls i.val)
    {J b : ℕ} (home : Fin J → Fin a.cube.cells) (headers : Fin J → Packing.BottomReports.BundleHeader)
    (ready : OpenSuffix.Ready (a.openInputs teamSlot.val (pub 0).val offsets ctl live ports J b home headers)
      (pub 0).val (readings (V).owned.val.2.2) w)
    (placement : OpenSuffix.Placement (a.openInputs teamSlot.val (pub 0).val offsets ctl live ports J b home headers)
      a.cube a.before (pub 0).val (readings (V).owned.val.2.2))
    {L : ReportLayout} {cs : List (ReportCell L)} {q : ReportCursor} {desc : ℕ}
    (seed : PreparedReportInput pub (V).controls.val.2.2 cs q desc)
    (allocated : ReportAllocation a.before a.after (a.cube.cellWriter (pub 0).val ctl decl.1) L cs q) :
    IssuedReportFrame a pub rep offsets ctl (F.dataDir.directory F.privatePlacement F.livePlacement).length := by
  have kept := issued_writer_host a U active teamSlot F seen ext route atOwned W done source
  have read := a.signed_report_words home headers (V).controls (V).reports seed kept ready placement allocated rfl
  exact e.issuedWriterFrame A addresses atFrame geometry controls W done read

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
