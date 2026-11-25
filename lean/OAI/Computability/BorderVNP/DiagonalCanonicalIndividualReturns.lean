import OAI.Computability.BorderVNP.DiagonalSourceReportVisitWords
import OAI.Computability.BorderVNP.DiagonalPositiveReportMap
import OAI.Computability.BorderVNP.DiagonalPositiveReportClaimFiber

/-! # Individual native returns from the supported core's canonical report family -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

/-- A successful chronological batch checks every privately indexed cell at
the same ordinal of its processor's returned report list. -/
theorem BatchReturns.cell {w n : ℕ} {l : ReportLayout} {ss : List (AssignedCell l)}
    {rs : List (ReportCell l)} {ts : List (List Bool × Bool)} (ok : BatchReturns w n ss rs ts)
    (i : ℕ) (hi : i<ss.length) (hj : i<rs.length) :
    ∃ ret,(ss[i]).Returns w n rs[i] ret := by
  induction ss generalizing rs ts i with
  | nil => simp at hi
  | cons s ss ih =>
    cases rs with
    | nil => simp at hj
    | cons r rs =>
      cases ts with
      | nil => exact False.elim ok
      | cons t ts =>
        cases i with
        | zero => exact ⟨t,ok.1⟩
        | succ i => exact ih ok.2 i (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)

end DiagonalTallyCellReports

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing CellSparse Packing.CellAddresses Packing.BottomReports Packing.Inherited
open RoutingISA RoutingISA.Evaluator DiagonalTallyCellReports DiagonalResidueRAM

variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P] {bits : P → ℕ}
    {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)
local notation3 (prettyPrint := false) "ss" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 (prettyPrint := false) "row" => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 (prettyPrint := false) "eqv" => R.physicalReportEquiv N cell siteID edgeID portID state owners slot ports
  owner bottom q raw R.cells (fun _ => rfl)

/-- Each owned cell inherits the passing guard of its processor's array. -/
theorem assignedAt_passing {w₀ input : ℕ} (pass : ∀ t c,c∈ss t → c.Passing w₀ input)
    (j : Σ t,Fin (R.cells t).length) : (row j.1 j.2).Passing w₀ input :=
  pass j.1 _ (List.mem_ofFn.mpr ⟨j.2,rfl⟩)

/-- On the actual positive report proposal obtained by inverting the core's
own report map, every assigned cell has its genuine native private return.
The report stream includes all teams and carries the actual physical data. -/
theorem canonical_individual_returns {w₀ input : ℕ} (pass : ∀ t c,c∈ss t → c.Passing w₀ input) :
    let rr := canonicalReports ss pass
    let proposal := (eqv).symm rr
    ∀ j : (t : Fin T) × Fin (R.cells t).length,∃ ret,(row j.1 j.2).Returns w₀ input
      (R.reportedWithTape (R.sourceReportStream proposal) (fun _ => 0) (R.order j)) ret := by
  intro rr proposal j
  have returned := (nativeReports_iff ss pass rr).2 rfl
  obtain ⟨ts,batch⟩ := returned j.1
  have fixedRows : (proposal j.1).val=(rr j.1).val :=
    R.physicalReportEquiv_symm_rows N cell siteID edgeID portID state owners slot ports owner bottom q raw
      R.cells (fun _ => rfl) rr j.1
  rw [←fixedRows] at batch
  have left : j.2.val<(ss j.1).length := by simpa only [ReceivedRows.assigned,List.length_ofFn] using j.2.isLt
  have right : j.2.val<(proposal j.1).val.length := by rw [(proposal j.1).length]; exact j.2.isLt
  have found := batch.cell j.2.val left right
  rw [R.reportedWithTape_source proposal j.1 j.2]
  simpa only [ReceivedRows.assigned,List.getElem_ofFn,List.get_eq_getElem,Fin.val_cast] using found

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
