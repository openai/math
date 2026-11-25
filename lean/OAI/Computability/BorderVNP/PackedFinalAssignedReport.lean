import OAI.Computability.BorderVNP.DiagonalNativeReportFiber
import OAI.Computability.BorderVNP.PackedFinalCellSupplement
import OAI.Computability.BorderVNP.CellReportObservationFacts
import OAI.Computability.BorderVNP.PackedFinalCellFixedUse
import OAI.Computability.BorderVNP.PackedOuterSignFree

/-! # Passing report fibers on the genuine owner-sorted terminal program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing Shortening CellAddresses CellSparse DiagonalTallyCellReports BottomReports
open RoutingISA RoutingISA.TypedBatch FiniteDiagonal.CellTrace
open scoped Classical
open private load from OAI.Computability.BorderVNP.PackedBankCellStatic

set_option maxHeartbeats 2000000
set_option maxRecDepth 18000

variable {D s m p : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {l : ReportLayout}
    (N : Network D P bits) (cell : N.Site → ℕ) (c : ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m)
    (portID : P ↪ Fin p) (owner : Fin s → ℕ) (state : N.Site → Site) (report : ReportCell l)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c (fun v => (state v).size)) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (bs : List Bundle) (obs : List (Bool × Option ℕ))

private noncomputable abbrev coreBank := CellAddresses.bank N cell c (fun v => (state v).size) g a x
private noncomputable abbrev reports := countFields (countBase N cell state c) l.gadgets l.countWidth
private noncomputable abbrev dir := directory owner N cell siteID edgeID portID state c (reports (l := l) N cell c state)

/-- The exact physical directory, wire choices and immutable weighted
metadata consumed by the native report-preparation uniqueness theorem. -/
noncomputable def assignedReport : AssignedCell l :=
  ⟨report,dir (l := l) N cell c siteID edgeID portID owner state,privateBits N cell state c,Fin.append g a,
    List.ofFn x,bs,obs⟩

/-- The actual sorted packed cell supplies the per-cell hypotheses of the
all-team native fiber. The original positive tag is checked once, before
guessing any reports. The actual tile visit bound controls every count word. -/
theorem assigned_passing (w order M : ℕ) (hw : 0<w) (howner : ∀ v, owner (siteID v)=cell v)
    (hin : ∀ v, (state v).incoming=incoming N v) (hs : ∀ v, (state v).Schema)
    (hlocal : ∀ v, (state v).Local) (hrel : ∀ v, (state v).RelativeBoxes)
    (unsigned : (dir (l := l) N cell c siteID edgeID portID owner state).SignFree)
    (observed : (dir (l := l) N cell c siteID edgeID portID owner state).guardedObservations
      (lookup (coreBank N cell c state g a x))=some obs)
    (ids : ∀ v ∈ sites siteID owner c, ∀ fs ∈ (state v).boxes, ∀ f ∈ fs, f.IDRange l.gadgets)
    (expanded : load N cell state c true ≤ M) (digits : M < 2^l.countWidth)
    (core : ∀ b ∈ bs, b.CorePass (coreBank N cell c state g a x))
    (sourceCounts : (report.bundles.map ReportBundle.useCount).sum=(bs.map Bundle.useBits).sum)
    (clock : ∀ z : Fin report.tailWidth → Bool,
      let task := withWiring (cellInput N cell siteID edgeID portID owner state c l.gadgets l.countWidth (List.ofFn x++List.ofFn z))
        (supplements (countBase N cell state c+l.gadgets*l.countWidth) bs)
      cellClock w task ≤ order^25) :
    (assignedReport N cell c siteID edgeID portID owner state report g a x bs obs).Passing w order := by
  let init := dir (l := l) N cell c siteID edgeID portID owner state
  let asg := assignedReport N cell c siteID edgeID portID owner state report g a x bs obs
  have pre : asg.pre=coreBank N cell c state g a x := by
    change List.ofFn (Fin.append g a) ++ List.ofFn x = List.ofFn g ++ (List.ofFn a ++ List.ofFn x)
    rw [List.ofFn_fin_append,List.append_assoc]
  have ps : asg.privateWires+asg.boundary.length=countBase N cell state c := by
    simp only [asg,assignedReport,List.length_ofFn,countBase]
  have stored (fs : List Factor) (hf : fs ∈ init.boxes) : ∀ f ∈ fs, f.IDRange l.gadgets := by
    obtain ⟨v,hv,here⟩ := List.mem_flatMap.mp hf
    exact ids v hv fs here
  obtain ⟨range,bounds⟩ := Directory.observed_range_counts stored _ observed
  have cap := (directory_load owner N cell siteID edgeID portID state c (reports (l := l) N cell c state)
    howner hs).2.2.2.trans expanded
  change asg.Passing w order
  refine ⟨hw,unsigned,?_,?_,?_,sourceCounts,range,fun i => ((bounds i.val).trans cap).trans_lt digits,?_,?_⟩
  · rw [ps]; rfl
  · intro tail
    rw [pre]
    exact (guarded_tail N cell c siteID edgeID portID owner state _ howner hin hs hlocal hrel g a x tail).trans observed
  · rw [pre]; exact core
  · exact directory_profileWidths owner N cell siteID edgeID portID state c _ (fun v _ => hs v)
  · intro z
    have bound := clock z
    change Copied.FitsClock (appendRows init (supplements (asg.privateWires+asg.boundary.length+l.gadgets*l.countWidth) bs))
      w order asg.privateWires (List.ofFn x++List.ofFn z)
    rw [ps]
    exact bound

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
