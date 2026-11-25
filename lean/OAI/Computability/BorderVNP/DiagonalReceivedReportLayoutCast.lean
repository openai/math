import OAI.Computability.BorderVNP.DiagonalSourceReportVisitWords
import OAI.Computability.BorderVNP.CubePhysicalReportReaders
import OAI.Computability.BorderVNP.CubePhysicalReceivedLedgerOrder
import OAI.Computability.BorderVNP.DiagonalSignedFinishFromReads

/-! # Rewriting the installed processor frame in a physical report ledger -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing Diagonal.CellEntries DiagonalTallyCellReports DiagonalTallyMaterialize DiagonalTallyAllocation
open RoutingISA RoutingISA.SignedTaskArena

variable {T C : ℕ} {l l' : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)

/-- Use the same physical roster after identifying its common report layout. -/
def atLayout (h : l=l') : ReceivedRows (fun _ : Fin T => l') C := h ▸ R

/-- Reindex the genuine finite report tapes together with their roster. -/
def tapesAtLayout (h : l=l') (tapes : ∀ t,ReportTape (R.cells t)) :
    ∀ t,ReportTape ((R.atLayout h).cells t) := by
  cases h
  exact tapes

/-- Transport the processor ownership of every physical roster ordinal. -/
theorem ownersAtLayout (h : l=l') (owner : Fin C → Fin T)
    (own : ∀ j : (t : Fin T) × Fin (R.cells t).length,owner (R.order j)=j.1)
    (j : (t : Fin T) × Fin ((R.atLayout h).cells t).length) : owner ((R.atLayout h).order j)=j.1 := by
  cases h
  exact own j

section Frame
open NativeLedger
variable {D B : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) {cell : N.Site → Fin sa.cube.cells} (control fieldWidth bodyCap : ℕ)
    {before after : ℕ}
local notation3 (prettyPrint := false) "chart" j =>
  reportLayout sa.before sa.after j control sa.p.parameters fieldWidth bodyCap sa.cube.stop
variable (rc : ReceivedRows (fun _ : Fin sa.cube.teams =>
      reportLayout sa.before sa.after before control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells) (frame : before=after)
    (slot : LiveBit N cell ↪ Slot sa.cube.n sa.cube.header.d sa.cube.header.blocks (sa.cube.h*sa.cube.b))
    (tags : N.Tables (Entry (Fin sa.p.parameters) (Fin sa.p.report.gadgets))) (x : Ports bits)
    (words : PowerWords (Fin sa.cube.teams) (Fin sa.p.parameters) (Fin sa.p.report.gadgets) B N tags)
    (label : Fin sa.cube.cells → Label (sa.cube.n+1) sa.cube.header.d)
    (owner : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (hosts : ∀ j : (u : Fin sa.cube.teams) × Fin (rc.cells u).length, pathCellOwner label owner a (rc.order j)=j.1)
    (t : Fin sa.cube.teams) (src : ∀ u,ReportAssignments (rc.cells u))
local notation3 (prettyPrint := false) "eqL" => congrArg (fun j => chart j) frame
local notation3 (prettyPrint := false) "inputs" =>
  rc.tapesAtLayout (l' := chart after) eqL (fun u => (reportAssignmentEquiv (rc.cells u)).symm (src u))
local notation3 (prettyPrint := false) "roster" => rc.atLayout (l' := chart after) eqL
local notation3 (prettyPrint := false) "stream" => fun u j =>
  if h : j<(reportBits ((roster).cells u)).length then inputs u ⟨j,h⟩ else false
local notation3 (prettyPrint := false) "ord(" rr "," own ")" =>
  Orders.withNativeVertices tags words label owner a t ((rr).ledgerOrder tags words label owner a own t)

/-- The finite digits and both sets of counting identities persist when the
installed frame is rewritten to the public operand of a given prefix. -/
def readersAtFrame (reads : ReportReaders (l := chart before) slot tags x words label owner a t (ord(rc,hosts))
    (rc.reportedWithTape (rc.sourceReportStream src) (fun _ => 0))) :
    ReportReaders (l := chart after) slot tags x words label owner a t (ord(roster,rc.ownersAtLayout eqL _ hosts))
      ((roster).reportedWithTape stream (fun _ => 0)) :=
  match frame with
  | rfl => reads

end Frame
end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
