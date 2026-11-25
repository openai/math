import OAI.Computability.BorderVNP.DiagonalWiredReturnedReportRows
import OAI.Computability.BorderVNP.DiagonalCheckedSeedReportRows

/-! # The returning owned cell's full augmented guard on its global row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open DiagonalTallyCellReports Packing.BottomReports CellSparse
open scoped Classical

variable {T C w n : ℕ} {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ)
    (assigned : ((t : Fin T) × Fin (R.cells t).length) → AssignedCell l)
    (same : ∀ j,(assigned j).report=(R.cells j.1).get j.2)
    (passes : ∀ j,(assigned j).Passing w n)
    (returns : ∀ j, ∃ ret,(assigned j).Returns w n (R.reportedWithTape tape start (R.order j)) ret)

include same passes returns in
/-- The actual returning cell has preserved its private and supplied extents.
Its complete supplemented directory sees its original observations on the full
returned bank, before the lead processor reads the tally. -/
theorem returnedCertificate (c : Fin C) :
    let j := R.order.symm c
    let s := assigned j
    let out := R.reportedWithTape tape start c
    out.privateWires=s.report.privateWires ∧ out.supplied=s.report.supplied ∧
    (appendRows s.initial (supplements (s.pre.length+l.gadgets*l.countWidth) s.bundles)).guardedObservations
      (lookup (s.pre++out.bits))=some s.observations := by
  obtain ⟨j,rfl⟩ := R.order.surjective c
  simp only [Equiv.symm_apply_apply]
  let s := assigned j
  let atBit := start j.1+(((R.cells j.1).take j.2.val).map ReportCell.tailWidth).sum
  have atRow : R.reportedWithTape tape start (R.order j)=s.report.withTape (tape j.1) atBit := by
    rw [same]
    exact R.reportedWithTape_at tape start j.1 j.2
  obtain ⟨ret,run⟩ := returns j
  rw [atRow] at run ⊢
  have actual := (passes j).canonical_augmented (s.report.withTape (tape j.1) atBit)
  obtain ⟨_,classify⟩ := s.native w n (passes j)
  have spelling := ((classify (tape j.1) atBit ret).mp run).1
  refine ⟨rfl,rfl,actual ?_ spelling⟩
  change ((tapeBundles (tape j.1) _ s.report.bundles).map ReportBundle.useCount).sum=(s.bundles.map Bundle.useBits).sum
  rw [tapeBundles_useCount]
  exact (passes j).uses

end Cube.Physical.NativeAssignments.ReceivedRows

namespace Cube.Physical.NativeAssignments.ReceivedRows

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited CellSparse DiagonalTallyCellReports
open scoped Classical
variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {l : ReportLayout} (R : ReceivedRows (fun _ : Fin T => l) C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle)
    (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 (prettyPrint := false) "key" => (fun v => (cell v).val)
local notation3 (prettyPrint := false) "progs" => (fun v => (state v).program)
local notation3 (prettyPrint := false) "size" => placedSize N state
local notation3 (prettyPrint := false) "guessed" c => privateWires N cell size c (raw c)
local notation3 (prettyPrint := false) "staged" c => privateStaging N cell size c (raw c)
local notation3 (prettyPrint := false) "supplied" c => pathSupply N cell edgeID portID owners slot ports q c
local notation3 (prettyPrint := false) "originalBank" c => bank N cell c size (guessed c) (staged c) (supplied c)


local notation3 (prettyPrint := false) "src" => fun j : (u : Fin T) × Fin (R.cells u).length =>
  R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw j.1 j.2
local notation3 (prettyPrint := false) "initial" c => FinalCell.directory owner N key siteID edgeID portID progs (Fin.val c)
  (R.countReports N cell state c)

/-- The actual physical cell ordinal reads its full accepted augmented guard on
the original staged assignment and the ordered bits returned to that ordinal. -/
theorem returnedCertificate_assignedAt {w order : ℕ} (tape : Fin T → ℕ → Bool) (start : Fin T → ℕ)
    (passes : ∀ j,(src j).Passing w order)
    (returns : ∀ j, ∃ ret,(src j).Returns w order (R.reportedWithTape tape start (R.order j)) ret)
    (c : Fin C) :
    let out := R.reportedWithTape tape start c
    (appendRows (initial c) (supplements ((originalBank c).length+l.gadgets*l.countWidth) (bottom c))).guardedObservations
      (lookup ((originalBank c)++out.bits))=some (src (R.order.symm c)).observations := by
  intro out
  let i := R.order.symm c
  let s := src i
  have atCell : R.order ⟨i.1,i.2⟩=c := R.order.apply_symm_apply c
  have p : s.pre=(originalBank c) :=
    (R.assignedAt_pre N cell siteID edgeID portID state owners slot ports owner bottom q raw i.1 i.2).trans
      (congrArg (fun u => originalBank u) atCell)
  have d : s.initial=(initial c) :=
    (R.assignedAt_directory N cell siteID edgeID portID state owners slot ports owner bottom q raw i.1 i.2).trans
      (congrArg (fun u => initial u) atCell)
  have rows : s.bundles=bottom c := congrArg bottom atCell
  have receipt := (R.returnedCertificate tape start src (fun _ => rfl) passes returns c).2.2
  change (appendRows s.initial (supplements (s.pre.length+l.gadgets*l.countWidth) s.bundles)).guardedObservations
    (lookup (s.pre++out.bits)) = some s.observations at receipt
  rw [d,p,rows] at receipt
  exact receipt

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
