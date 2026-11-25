import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports
import OAI.Computability.BorderVNP.DiagonalReportArgumentEmission

/-! # Report arrays under equality of the source labels

The selector, owner function and payload stay indexed by the same routed
assignment while the resident writer's cell label is identified with the
label of the issued packet. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments
open DiagonalTallyCellReports ReportDirectory

variable {D R bundles : ℕ} {P : Type} {bits : P → ℕ}
    {ar : CubeArena.Layout} {N : Network D P bits} {cell : N.Site → Fin ar.cells}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {slot : LiveBit N cell ↪ Slot ar.n ar.header.d ar.header.blocks (ar.h*ar.b)}
    {resident packet : Fin ar.cells → Label (ar.n+1) ar.header.d}
    {charts : Fin (R+1) → ReportLayout} {home : Fin bundles → Fin ar.cells} {bodies : Fin bundles → ReportBundle}
    {supplied wires : ℕ → ℕ} {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners} {u : Fin (R+1)}
    {localChart : ReportLayout} {cells : List (ReportCell localChart)}

local notation3 (prettyPrint := false) "src(" lab ")" =>
  routedSourceReports ar N cell owners slot lab charts home bodies supplied wires

/-- Read the issued and resident labels at one physical routed assignment.
The last equality transports an emitted report back to its resident array. -/
theorem SameReportCells.atPacketLabel (same : SameReportCells cells ((src(resident)).cells q u))
    (accepted : (src(resident)).pins q) (names : packet=resident) :
    (src(packet)).pins q ∧
      SameReportCells cells ((src(packet)).cells q u) ∧ (src(packet)).cells q u=(src(resident)).cells q u := by
  subst packet
  exact ⟨accepted,same,rfl⟩

end RoutingISA.Evaluator.SignedPrep

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords CellPacket CellPacket.Supplement
open TypedTaskBuilder FragmentRows SignedTaskArena DiagonalTallyCellReports DiagonalTallyAllocation

/-- Transport the report list of this emission while fixing its native return,
its memory, and the concrete emitted row object. -/
theorem ReportArgumentEmission.onReportRows
    {w n p d H description ctl offsets length team live ports : ℕ} {a : SignedTaskArena.Layout} {O E : Type}
    {G : SiteWords.Directory (Fin n) O (a.cube.cells+1)} {ptr : O → E} {base : ℕ → ℕ} {slot : O → ℕ}
    {fs : O → List Factor} {pub : Arg → Word w} {m : Memory w} {s : RoutingISA.Bank w} {mac : TeamOpcode.Macros w 8}
    {rl : ReportLayout} {packet resident : List (ReportCell rl)} {q : ReportCursor}
    {r : Returns prepareCellReports pub mac s m}
    {fit : (FragmentRows.Layout.fromFrame (readings pub 0) (readings r.val.2.2)).Fits w (readings r.val.2.2)}
    {cc : a.fragments.cells=(FragmentRows.Layout.fromFrame (readings pub 0) (readings r.val.2.2)).cells}
    {e : SparseEmission a _ r.val.2.2 fit cc}
    (rows : packet=resident)
    (sent : ReportArgumentEmission (p:=p) (d:=d) (H:=H) (length:=length) (description:=description)
      (ctl:=ctl) (offsets:=offsets) (team:=team) (live:=live) (ports:=ports) G ptr base slot fs packet q r e) :
    ReportArgumentEmission (p:=p) (d:=d) (H:=H) (length:=length) (description:=description)
      (ctl:=ctl) (offsets:=offsets) (team:=team) (live:=live) (ports:=ports) G ptr base slot fs resident q r e := by
  subst resident
  exact sent

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
