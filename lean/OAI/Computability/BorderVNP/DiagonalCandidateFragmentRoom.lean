import OAI.Computability.BorderVNP.DiagonalSignedBareFragmentRoom
import OAI.Computability.BorderVNP.DiagonalFrozenPostReportWords
import OAI.Computability.BorderVNP.DiagonalCandidateReturnedRouteOwner
import OAI.Computability.BorderVNP.DiagonalPublishedHostCables

/-! # The fragment directory of one returning candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option quotPrecheck false
set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock Routing
open BorderVNP.Cube Physical Tally TeamContraction JointHeader PackedHistoryCircuit
open FiniteEvaluator CellMacro.Generator DiagonalTallyAllocation DiagonalTallyCellReports
open Packing Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs GeometryAdvice
open DiagonalTallyPacketEmit

variable {R w budget s np bits lenBits cellBits dim : ℕ} {P σ : Type*} [Fintype P] [Fintype σ]
    {widths : P → ℕ} (task : SignedTaskArena.Layout) {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration task.cube.n task.cube.header.d} {group : Fin task.cube.header.d → Fin (R+1)}
    {frame receiving : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub ep : Arg → Word w} {mac em : TeamOpcode.Macros w 8} {reg bank : Bank w} {mem before : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin task.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {N : Network dim P widths} {cell : N.Site → Fin task.cube.cells} {A : Type*} {recv : A → Fin task.cube.cells} {amount : A → ℕ}
    (site : CandidateSite (R:=R) (X:=budget) task.cube D pp lp raw owner decl group frame receiving pins fields f guess pub mac reg mem
      host key sizes N cell recv amount)
    {prof gates words width tail gap bankBits : ℕ} {original : Fin D.entries → N.Site} {live : Fin (D.teams*D.sites) → P}
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin np)
    (F : Fields s task.cube.cables np task.cube.cells cellBits lenBits bits σ) {x : σ → Bool}
local notation3 (prettyPrint := false) "first" => receiving+7*D.candidates
local notation3 (prettyPrint := false) "origin" => Allocation.dest first prof gates words width
local notation3 (prettyPrint := false) "tables" => bases origin task.cube.cables task.cube.cells D.entries
local notation3 (prettyPrint := false) "ctl" => controlsBase origin task.cube.cables task.cube.cells D.entries (D.teams*D.sites)
local notation3 (prettyPrint := false) "prior" => readings site.published.val.2.2
local notation3 (prettyPrint := false) "written" => readings site.receipt.history.dataInput

/-- The arbitrary report returned on this candidate's owned memory yields its
complete issued directory, all 37 controls and the sparse receiving geometry. The only
run after the owned return used here is the control opener and report reader. -/
theorem CandidateSite.issuedFragmentRoom (u : Fin (R+1))
    (opened : Returns Evaluator.SignedPrep.controls ep em bank before)
    (reported : Returns prepareCellReports ep em opened.val.2.1 opened.val.2.2)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout}
    {description : ℕ} (hdr : Fin D.entries → BottomReports.BundleHeader)
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (allocation : ∀ c, suppliedSize N cell c+gap ≤ task.cube.cellStride)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings site.geometry))
    (place : (privateLayout frame origin task.cube.cables task.cube.cells D.entries D.description gap).Image
      (readings site.geometry) D.entries (readings site.middle))
    (geomHeader : Header frame origin task.cube.cables task.cube.cells D.entries (readings site.geometry))
    {readerIn readerGuess readerGates : ℕ} (high : task.endAddress w readerIn readerGuess readerGates < 2^w)
    (reserve : task.cube.header.header=Allocation.stop first prof gates words width w)
    (complete : task.cube.cables*3+(RoutingOutputs.count task.cube.cables task.cube.cells D.entries (D.teams*D.sites)+
      ((task.cube.cells+(D.entries+task.cube.cells))+(37+tail))) ≤ words)
    {input : ℕ → ℕ} {home : Fin D.entries → Fin task.cube.cells} (native : NativeEntry task.cube frame ctl decl.1 R input prior written)
    (control : FrozenControlEntry task (task.openInputs u.val frame (tables).ends ctl (tables).livePairs
      (D.teams*D.sites) D.entries bankBits home hdr) frame (ep 0).val ctl (tables).ends w
      (fun c => suppliedSize N cell c) written (readings before))
    (seed : PreparedReportInput ep opened.val.2.2 cs q description)
    (alloc : ReportAllocation task.before task.after banks l cs q) (bankAt : banks.bankStart=task.cube.cellBank) :
    IssuedReportFrame task ep reported.val.2.2 (tables).ends ctl (D.directory pp lp).length := by
  have head : readings ep 0=frame := control.frame
  have low : frame+112≤receiving := site.origin ▸ site.placement.rawStart
  have rawAt : readings site.middle (frame+8)=receiving := site.origin ▸ site.placement.pointers.1
  have actual : readings (Directory.ISA.publish site.middle frame receiving (D.directory pp lp))=prior := by
    rw [site.actual,site.origin]
  have header := published_routing_header pp lp place geomHeader low (by unfold Allocation.dest Allocation.temp; omega)
  have ends := site.rows.choose_spec.choose
  rw [site.origin] at ends
  have keep : CubeAllocation.HostRetention task.cube frame prior written (readings before) :=
    ⟨control.retained.primary,fun j hj h₀ h₁ => (control.retained.lower j hj h₀ h₁).trans (native.low j hj),control.retained.tables⟩
  have one (j : ℕ) (small : j<112) (ne₁ : j≠13) (ne₂ : j≠46) : prior (frame+j)=readings before (frame+j) :=
    (keep.lower _ (by have := keep.primary; omega) (by omega) (by omega)).symm
  have room : ctl+37 ≤ task.cube.header.header := by
    rw [reserve]
    unfold RoutingOutputs.count at complete
    dsimp only [controlsBase,bases,Allocation.stop,Allocation.packed,Allocation.dense]
    omega
  have controlsAt (i : Fin 37) : written (ctl+i.val)=task.controls i.val :=
    (control.retained.lower _ (by have := i.isLt; omega) (by have := control.frameEnd; omega)
      (by have := control.frameEnd; omega)).symm.trans (control.controls i)
  have rest := task.signed_fragment_room ep u opened reported N cell aux siteID edgeID portID F D pp lp
    receiving prof gates words width tail (geom:=site.geometry) (placed:=site.middle) («written»:=written)
    (input:=input) (gap:=gap) (original:=original) (live:=live) (bankBits:=bankBits) (l:=l) (cs:=cs) (q:=q)
    («banks»:=banks) (description:=description) home hdr rep codes fieldFit
    (fun c => (Nat.le_add_right _ _).trans (allocation c)) image (head.symm ▸ place)
    high reserve complete (head.symm ▸ low) (head.symm ▸ rawAt) site.input.records controlsAt decl.1
  dsimp only at rest
  rw [head] at rest
  have ready := control.ready
  change OpenSuffix.Ready _ (readings ep 0) _ _ at ready
  rw [head] at ready
  rw [actual] at header rest
  have clean := rest header
    ((one 92 (by decide) (by decide) (by decide)).trans control.controlWord)
    ((one 72 (by decide) (by decide) (by decide)).trans control.placement.pointer)
    ends native keep ready control.placement seed alloc bankAt
  change ∃ fr : FragmentDirectoryInput ep reported.val.2.2, _
  simpa only [show (ep 0).val=frame from head] using clean

/-- The arbitrary report returned on this candidate's owned memory yields its
actual compact delivery count, sparse offsets and cell directory. The only
run after the owned return used here is the control opener and report reader. -/
theorem CandidateSite.fragmentRoom (u : Fin (R+1))
    (opened : Returns Evaluator.SignedPrep.controls ep em bank before)
    (reported : Returns prepareCellReports ep em opened.val.2.1 opened.val.2.2)
    {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout}
    {description : ℕ} (hdr : Fin D.entries → BottomReports.BundleHeader)
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (allocation : ∀ c, suppliedSize N cell c+gap ≤ task.cube.cellStride)
    (image : Image F (siteID ∘ original) (portID ∘ live) x origin (readings site.geometry))
    (place : (privateLayout frame origin task.cube.cables task.cube.cells D.entries D.description gap).Image
      (readings site.geometry) D.entries (readings site.middle))
    (geomHeader : Header frame origin task.cube.cables task.cube.cells D.entries (readings site.geometry))
    {readerIn readerGuess readerGates : ℕ} (high : task.endAddress w readerIn readerGuess readerGates < 2^w)
    (reserve : task.cube.header.header=Allocation.stop first prof gates words width w)
    (complete : task.cube.cables*3+(RoutingOutputs.count task.cube.cables task.cube.cells D.entries (D.teams*D.sites)+
      ((task.cube.cells+(D.entries+task.cube.cells))+(37+tail))) ≤ words)
    {input : ℕ → ℕ} {home : Fin D.entries → Fin task.cube.cells} (native : NativeEntry task.cube frame ctl decl.1 R input prior written)
    (control : FrozenControlEntry task (task.openInputs u.val frame (tables).ends ctl (tables).livePairs
      (D.teams*D.sites) D.entries bankBits home hdr) frame (ep 0).val ctl (tables).ends w
      (fun c => suppliedSize N cell c) written (readings before))
    (seed : PreparedReportInput ep opened.val.2.2 cs q description)
    (alloc : ReportAllocation task.before task.after banks l cs q) (bankAt : banks.bankStart=task.cube.cellBank) :
    ∃ fr : FragmentDirectoryInput ep reported.val.2.2, fr.layout.count=(D.directory pp lp).length ∧
      task.fragments.cells=fr.layout.cells ∧ fr.layout.host.count=task.cube.cables ∧
      FragmentRows.SparseGeometry task fr.layout (tables).ends ctl := by
  obtain ⟨fr,_,count,_,cells,cables,_,_,geo⟩ := site.issuedFragmentRoom task aux siteID edgeID portID F u opened
    reported hdr rep codes fieldFit allocation image place geomHeader high reserve complete native control seed alloc bankAt
  exact ⟨fr,count,cells,cables,geo⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
