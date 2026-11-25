import OAI.Computability.BorderVNP.DiagonalPositiveCoreAbsent
import OAI.Computability.BorderVNP.DiagonalPositiveReportClaimFiber

/-! # Passing private native weights force all original cell guards -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs CellSparse
open RoutingISA.Evaluator RoutingISA.CompactMachine DiagonalTallyCellReports VPVNP.BurstRAM
open scoped Classical BigOperators

variable {D C ns ne np n d blocks b h K s T w order : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (reports : Fin C → List (List ℕ))
    (q : Routed (b:=b) (s:=s) owners)
local notation3 "size" => placedSize N state
variable (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)
    {layout : Fin T → ReportLayout} (ss : ∀ u,List (AssignedCell (layout u)))

/-- Identify every original finite cell with the actual received owned row
at its native team. The table and the bank include its guessed internal
wires, retained-site staging and addressed path supply. -/
structure OriginalRows where
  /-- Actual local report ordinal at the native owner. -/
  atRow : Fin C → Σ u : Fin T,Fin (ss u).length
  directory : ∀ c, ((ss (atRow c).1).get (atRow c).2).initial=
    FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID (fun v => (state v).program) c.val (reports c)
  coreBank : ∀ c, ((ss (atRow c).1).get (atRow c).2).pre=
    bank N cell c size (privateWires N cell size c (raw c)) (privateStaging N cell size c (raw c))
      (pathSupply N cell edgeID portID owners slot ports q c)
  unsigned : ∀ c,((ss (atRow c).1).get (atRow c).2).initial.SignFree

variable (image : OriginalRows N cell siteID edgeID portID state owners slot ports owner reports q raw ss)
    (ho : ∀ v,owner (siteID v)=(cell v).val) (hin : ∀ v,(state v).program.incoming=incoming N v)
    (schema : ∀ v,(state v).program.Schema) (locality : ∀ v,(state v).program.Local)
    (relative : ∀ v,(state v).program.RelativeBoxes)

local notation3 "guard" => GuardedCores N cell siteID edgeID portID state owners slot ports owner reports
local notation3 "dir" c => FinalCell.directory owner N (fun v => (cell v).val) siteID edgeID portID (fun v => (state v).program) (Fin.val c) (reports c)
local notation3 (prettyPrint := false) "before" c => bank N cell c size (privateWires N cell size c (raw c)) (privateStaging N cell size c (raw c))
  (pathSupply N cell edgeID portID owners slot ports q c)

include ho hin schema locality relative in
/-- Failure is preserved on every possible byte suffix at the actual ordinal. -/
theorem OriginalRows.absent_tail (c : Fin C) (bad : (dir c).guardedObservations (lookup (before c))=none) :
    let j := image.atRow c
    let A := (ss j.1).get j.2
    ∀ tail,A.initial.guardedObservations (lookup (A.pre++tail))=none := by
  intro j A tail
  change ((ss (image.atRow c).1).get (image.atRow c).2).initial.guardedObservations
    (lookup (((ss (image.atRow c).1).get (image.atRow c).2).pre++tail))=none
  rw [image.directory c,image.coreBank c]
  exact (FinalCell.finite_guarded_tail N cell c siteID edgeID portID owner state (reports c) ho hin schema
    locality relative _ _ _ tail).trans bad

include ho hin schema locality relative in
/-- At a failed original cell no actual clocked validator can return, for
either sign and for any received report digits. -/
theorem OriginalRows.no_return (c : Fin C) (bad : (dir c).guardedObservations (lookup (before c))=none) :
    let j := image.atRow c
    let A := (ss j.1).get j.2
    0<w → A.initial.ProfileWidths →
    (∀ x : Fin A.report.tailWidth → Bool,FiniteDiagonal.CellTrace.Copied.FitsClock A.augmented w order A.privateWires
      (A.boundary++List.ofFn x)) →
    ∀ (r : ReportCell (layout j.1)), r.bits.length=A.report.tailWidth → ∀ ret,¬ A.Returns w order r ret := by
  intro j A hw profile clock r len ret
  exact A.no_return (image.unsigned c) (OriginalRows.absent_tail N cell siteID edgeID portID state owners slot ports owner reports q raw ss image ho hin schema locality relative c bad) hw profile clock r len ret

variable {gen : CellMacro.Generator.Fragment CellMacro.Generator.IO} {Prefix : Fin T → Type}
    {pub : Fin T → RoutingISA.Arg → Word w} {mem : ∀ u,Prefix u → Memory w}
    {cells : ∀ u a,GeneratedCells gen order (pub u) (mem u a)} {pre : ∀ u, Prefix u}
    (J : JoinedCells pub mem cells pre) (z : J.Private)
    (r : NativeReports ss) (physical : J.ReportImage z ss r)

include image physical ho hin schema locality relative in
/-- Recover all original compact guards from the true positive product.
The supplied pin condition is checked by the native control visits before
the report-stage state exists. Failed original cells have zero local weight
on every proposed report, including otherwise valid subtotal headers. -/
theorem OriginalRows.guarded_of_nonzero (pins : Path.Pins N cell slot (rawPath N cell edgeID state owners q raw))
    (weight : J.privateWeight z ≠ 0) : guard q raw := by
  refine ⟨pins,?_⟩
  intro c
  let j := image.atRow c
  let A := (ss j.1).get j.2
  let row := (r j.1).val.get (Fin.cast (assignedRows_length (r j.1)).symm j.2)
  cases obs : (dir c).guardedObservations (lookup (before c)) with
  | some os => exact ⟨os,rfl⟩
  | none =>
    have zero : A.reportWeight row=0 := A.reportWeight_zero (image.unsigned c)
      (OriginalRows.absent_tail N cell siteID edgeID portID state owners slot ports owner reports q raw ss image ho hin schema locality relative c obs) row
    have nonzero := (Finset.prod_ne_zero_iff.mp weight) (physical.number ⟨j.1,j.2⟩) (Finset.mem_univ _)
    rw [physical.directory,physical.privateBits,physical.external,← List.append_assoc] at nonzero
    exact (nonzero zero).elim

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
