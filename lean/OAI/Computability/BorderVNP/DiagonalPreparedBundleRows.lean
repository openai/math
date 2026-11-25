import OAI.Computability.BorderVNP.DiagonalSparsePreparedReports
import OAI.Computability.BorderVNP.DiagonalLocalTapeDirectory

/-! # The bundle inputs of each actual row of a prepared native report scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA VPVNP.BurstRAM
open private originalInputs from OAI.Computability.BorderVNP.RoutingISASparseReportSources

variable {l : ReportLayout} {w description : ℕ}

/-- The report cursor advances through exactly the earlier rows of this local scan. -/
def previousReportCursor (cs : List (ReportCell l)) (q : ReportCursor) (i : ℕ) : ReportCursor :=
  (cs.take i).foldl (fun previous cell => cell.after previous) q

/-- The numeric memory immediately before a row is the ordered image of the
preceding compiled cell writes. -/
def previousReportMemory (cs : List (ReportCell l)) (q : ReportCursor) (m : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  cellImages (cs.take i) q m

private theorem cellInput_get (cs : List (ReportCell l)) (q : ReportCursor) (base : ℕ) (m : ℕ → ℕ)
    (inputs : cellInputs w description cs q base m) (i : Fin cs.length) :
    (cs.get i).Input (previousReportCursor cs q i.val) w (base+6*i.val) description (previousReportMemory cs q m i.val) := by
  induction cs generalizing q base m with
  | nil => exact Fin.elim0 i
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.val_zero,Nat.mul_zero,Nat.add_zero,previousReportCursor,previousReportMemory,List.take_zero,
        List.foldl_nil,cellImages,List.get_cons_zero] using inputs.1
    · have after := ih (c.after q) (base+6) (c.image q m) inputs.2 j
      simpa only [Fin.val_succ,previousReportCursor,previousReportMemory,List.take_succ_cons,List.foldl_cons,cellImages,
        List.get_cons_succ',Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm 6 (6*j.val)] using after

/-- Extract the actual native private-bundle scanner inputs at any compact
row, with the same count image and six-word bundle pointer as the compiler. -/
theorem PreparedReportInput.bundleAt {pub : Arg → Word w} {mem : Memory w} {cs : List (ReportCell l)} {q : ReportCursor}
    (seed : PreparedReportInput pub mem cs q description) (i : Fin cs.length) :
    let c := cs.get i
    let prev := previousReportCursor cs q i.val
    bundleInputs w l description c.bundles (c.localStart prev) (l.bundleTable+6*c.first)
      ((c.countFrame prev).image .count (previousReportMemory cs q (readings mem) i.val)) :=
  (cellInput_get cs q l.headers (readings mem) (originalInputs seed) i).1.bundles

open RoutingISA.TypedTaskBuilder

/-- The source reports visited by the actual local owner scan, indexed using
the global cell determined by the running count. -/
noncomputable def visitedReportRows (rows : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l) :=
  List.ofFn fun i : Fin (rows.before raw rows.cells) => atCell (globalCell rows.toLayout raw i.val)

/-- This compact list is exactly the increasing restriction of all global
cells to the processor's local owner word. -/
theorem visitedReportRows_scan (rows : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l) :
    visitedReportRows rows raw atCell =
      ((List.range rows.cells).filter fun c => decide (rows.owner raw c=rows.team)).map atCell := by
  rw [←globalCell_prefix rows.toLayout raw rows.cells le_rfl]
  simp only [visitedReportRows,List.map_ofFn,Function.comp_def]

/-- Each physically owned global cell occurs at the index given by the owner
prefix counter, even when a different team proposed different owners. -/
theorem visitedReportRows_owned (rows : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l)
    (c : ℕ) (realCell : c<rows.cells) (owned : rows.owner raw c=rows.team) :
    let cs := visitedReportRows rows raw atCell
    ∃ j : Fin cs.length, j.val=rows.before raw c ∧ cs.get j=atCell c := by
  have member : c ∈ ((List.range rows.cells).filter fun x => decide (rows.owner raw x=rows.team)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr realCell,by simp only [owned,decide_true]⟩
  rw [←globalCell_prefix rows.toLayout raw rows.cells le_rfl,List.mem_ofFn] at member
  obtain ⟨i,address⟩ := member
  have previous := (global_spec rows.toLayout raw i.isLt).2.2
  change globalCell rows.toLayout raw i.val=c at address
  rw [address] at previous
  let cs := visitedReportRows rows raw atCell
  let j : Fin cs.length := ⟨i.val,by simpa only [cs,visitedReportRows,List.length_ofFn] using i.isLt⟩
  have selected : cs.get j = atCell c := by
    simpa only [cs,j,visitedReportRows,List.get_eq_getElem,List.getElem_ofFn] using congrArg atCell address
  exact ⟨j,previous.symm,selected⟩

/-- A prepared scanner yields the compiler's actual bundle inputs at the
local prefix length of each owned global ordinal. -/
theorem PreparedReportInput.ownedBundleAt {pub : Arg → Word w} {mem : Memory w} {q : ReportCursor}
    (rows : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l)
    (seed : PreparedReportInput pub mem (visitedReportRows rows raw atCell) q description)
    (c : ℕ) (realCell : c<rows.cells) (owned : rows.owner raw c=rows.team) :
    let cs := visitedReportRows rows raw atCell
    let previous := previousReportCursor cs q (rows.before raw c)
    let r := atCell c
    bundleInputs w l description r.bundles (r.localStart previous) (l.bundleTable+6*r.first)
      ((r.countFrame previous).image .count (previousReportMemory cs q (readings mem) (rows.before raw c))) := by
  let cs := visitedReportRows rows raw atCell
  obtain ⟨j,previous,selected⟩ := visitedReportRows_owned rows raw atCell c realCell owned
  have native := seed.bundleAt j
  change bundleInputs w l description (cs.get j).bundles ((cs.get j).localStart (previousReportCursor cs q j.val))
    (l.bundleTable+6*(cs.get j).first) (((cs.get j).countFrame (previousReportCursor cs q j.val)).image .count
      (previousReportMemory cs q (readings mem) j.val)) at native
  rw [selected,previous] at native
  exact native

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
