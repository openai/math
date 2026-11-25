import OAI.Computability.BorderVNP.DiagonalPositiveUncheckedCores

/-! # Original private banks at their physical report ordinals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs CellSparse
open DiagonalTallyCellReports
open scoped Classical

/-- The owned rows in native visitation order, with their published global cell
numbers. Empty teams and cells with empty bundle inventories are included. -/
structure ReceivedRows {T : ℕ} (layout : Fin T → ReportLayout) (C : ℕ) where
  /-- The physically published compact report rows of each team. -/
  cells : ∀ u, List (ReportCell (layout u))
  /-- The global numeral for every compact team-local ordinal. -/
  order : (Σ u : Fin T, Fin (cells u).length) ≃ Fin C
  number : ∀ u i, ((cells u).get i).number=(order ⟨u,i⟩).val

variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle)
    (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 "key" => (fun v => (cell v).val)
local notation3 "progs" => (fun v => (state v).program)
local notation3 "size" => placedSize N state
local notation3 "guessed" c => privateWires N cell size c (raw c)
local notation3 "staged" c => privateStaging N cell size c (raw c)
local notation3 "supplied" c => pathSupply N cell edgeID portID owners slot ports q c
local notation3 "originalBank" c => bank N cell c size (guessed c) (staged c) (supplied c)

/-- Native addresses of all report count bits at the team which visits the cell. -/
noncomputable def ReceivedRows.countReports (c : Fin C) : List (List ℕ) :=
  let l := layout (R.order.symm c).1
  countFields (FinalCell.countBase N key progs c.val) l.gadgets l.countWidth

local notation3 "fields" => R.countReports N cell state
local notation3 "initial" c => FinalCell.directory owner N key siteID edgeID portID progs (Fin.val c) (fields c)

/-- Attach the routed supply and the original private bank to the physical row.
The observation payload uses the actual guard result even before acceptance
has been checked. -/
noncomputable def ReceivedRows.assignedAt (u : Fin T) (i : Fin (R.cells u).length) : AssignedCell (layout u) :=
  let c := R.order ⟨u,i⟩
  let widths := Packing.FinalReports.bank_sizes N cell progs c
  FinalCell.assignedReport N key c.val siteID edgeID portID owner progs ((R.cells u).get i)
    ((guessed c) ∘ Fin.cast widths.1) ((staged c) ∘ Fin.cast widths.2.1)
    ((supplied c) ∘ Fin.cast widths.2.2) (bottom c)
    (((initial c).guardedObservations (lookup (originalBank c))).getD [])

local notation3 "row" => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw

/-- The directory is assembled at the published global number of this very row. -/
theorem ReceivedRows.assignedAt_directory (u : Fin T) (i : Fin (R.cells u).length) :
    (row u i).initial=initial (R.order ⟨u,i⟩) := by
  simp only [assignedAt,FinalCell.assignedReport,countReports,Equiv.symm_apply_apply]

/-- The compact validator receives the original guessed, staged and supplied
bits consecutively, with precisely the same ordering under the native numeral. -/
theorem ReceivedRows.assignedAt_pre (u : Fin T) (i : Fin (R.cells u).length) :
    (row u i).pre=originalBank (R.order ⟨u,i⟩) := by
  let c := R.order ⟨u,i⟩
  let widths := Packing.FinalReports.bank_sizes N cell progs c
  let g := (guessed c) ∘ Fin.cast widths.1
  let a := (staged c) ∘ Fin.cast widths.2.1
  let x := (supplied c) ∘ Fin.cast widths.2.2
  change List.ofFn (Fin.append g a) ++ List.ofFn x=originalBank c
  rw [List.ofFn_fin_append,List.append_assoc]
  exact FinalTies.bank_nat N cell c progs (guessed c) (staged c) (supplied c)

/-- A successful original guard supplies the actual observation list in the
received cell, including the case of a successful empty observation list. -/
theorem ReceivedRows.assignedAt_observed (u : Fin T) (i : Fin (R.cells u).length)
    (passed : ∃ os, (initial (R.order ⟨u,i⟩)).guardedObservations
      (lookup (originalBank (R.order ⟨u,i⟩)))=some os) :
    (row u i).initial.guardedObservations (lookup (row u i).pre)=some (row u i).observations := by
  obtain ⟨os,ok⟩ := passed
  rw [R.assignedAt_directory,R.assignedAt_pre,ok]
  change some os=some (((initial (R.order ⟨u,i⟩)).guardedObservations
    (lookup (originalBank (R.order ⟨u,i⟩)))).getD [])
  rw [ok]
  rfl

/-- All physical private assignments on one team, in the visit order of
its frozen report rows. -/
noncomputable def ReceivedRows.assigned (u : Fin T) : List (AssignedCell (layout u)) :=
  List.ofFn (row u)

local notation3 "allRows" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw

/-- The native report-stage input is exactly the immutable row list on which
the assignment was constructed. -/
theorem ReceivedRows.assigned_report (u : Fin T) :
    (allRows u).map AssignedCell.report=R.cells u := by
  simp [assigned,assignedAt,FinalCell.assignedReport,List.map_ofFn,Function.comp_def]

/-- Every original cell occurs once at its actual local ordinal. This
receipt is defined on arbitrary original banks, including failed guards. -/
noncomputable def OriginalRows.ofReceived (unsigned : ∀ v,(state v).program.SignFree) :
    OriginalRows N cell siteID edgeID portID state owners slot ports owner fields q raw allRows := by
  let ordinal (c : Fin C) : Σ u : Fin T, Fin (allRows u).length :=
    let j := R.order.symm c
    ⟨j.1,Fin.cast (List.length_ofFn (f:=row j.1)).symm j.2⟩
  have dir (c : Fin C) : ((allRows (ordinal c).1).get (ordinal c).2).initial=initial c := by
    let j := R.order.symm c
    have h := R.assignedAt_directory N cell siteID edgeID portID state owners slot ports owner bottom q raw j.1 j.2
    change (row j.1 j.2).initial=initial (R.order j) at h
    rw [show R.order j=c from R.order.apply_symm_apply c] at h
    simpa [ordinal,ReceivedRows.assigned,j] using h
  refine ⟨ordinal,dir,?_,?_⟩
  · intro c
    let j := R.order.symm c
    have h := R.assignedAt_pre N cell siteID edgeID portID state owners slot ports owner bottom q raw j.1 j.2
    change (row j.1 j.2).pre=originalBank (R.order j) at h
    rw [show R.order j=c from R.order.apply_symm_apply c] at h
    simpa [ordinal,ReceivedRows.assigned,j] using h
  · intro c
    rw [dir c]
    exact sortedDirectory_signFree N key siteID edgeID portID owner progs c.val (fields c) unsigned

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
