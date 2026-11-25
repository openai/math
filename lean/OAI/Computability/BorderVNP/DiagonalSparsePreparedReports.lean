import OAI.Computability.BorderVNP.DiagonalSparseReportSources
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # The charged report scanner on the selected global source-cell order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA
open private redecode redecodeCell from OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows

/-- Changing the sampled digits of a report assignment preserves every input
condition at the scanner entry, even when the new digits will fail in the cell. -/
theorem PreparedReportInput.of_same {w description : ℕ} {L : ReportLayout} {pub : Arg → Word w}
    {m : Memory w} {cs ds : List (ReportCell L)} {q : ReportCursor}
    (seed : PreparedReportInput pub m cs q description) (same : eraseReportBits cs=eraseReportBits ds) :
    PreparedReportInput pub m ds q description := by
  have count : cs.length=ds.length := by
    simpa only [eraseReportBits,tapeCells_length] using congrArg List.length same
  refine ⟨seed.framePointer,seed.first,count ▸ seed.seeded,seed.frameRoom,seed.controlRoom,count ▸ seed.headerRoom,
    seed.rawRoom,?_⟩
  intro tape
  have words : tapeCells tape 0 cs=tapeCells tape 0 ds := by
    simpa only [eraseReportBits,redecode] using congrArg (tapeCells tape 0) same
  exact words ▸ seed.inputs tape

/-- The erasure used by the native report scanner ignores an independently
chosen input tape and offset at every cell of the selected list. -/
theorem eraseReportBits_localTapes {α : Type*} {L : ReportLayout} (indices : List α) (source : α → ReportCell L)
    (tape : α → ℕ → Bool) (start : α → ℕ) :
    eraseReportBits (indices.map fun i => (source i).withTape (tape i) (start i)) =
      eraseReportBits (indices.map source) := by
  have aux (p : ℕ) : tapeCells (fun _ => false) p (indices.map fun i => (source i).withTape (tape i) (start i)) =
      tapeCells (fun _ => false) p (indices.map source) := by
    induction indices generalizing p with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons,tapeCells,redecodeCell,ReportCell.withTape_tailWidth,ih]
  exact aux 0

end DiagonalTallyCellReports

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open DiagonalTallyCellReports DiagonalTallyCellReports.ReportDirectory TypedTaskBuilder

variable {Site E I P A : Type} [Fintype P] {w : ℕ} {a : CubeArena.Layout}
    {D : LengthDeclaration a.n a.header.d} {label : Fin a.cells → Label (a.n+1) a.header.d}
    {recv : A → Fin a.cells} {assigned : ℕ → ℕ}
    {r description p d R H B : ℕ} {team : Fin (r+1)} {pub : Arg → Word w} {m : Memory w}
    {src : SparseCallInput pub m} {f : FragmentRows.Layout} {bank : ℕ → ℕ} {l : CellControlRows.Layout} {mem : ℕ → ℕ}

variable {inputs : A → ℕ}
    (S : SparseReportSources Site E I P a D label recv inputs assigned team.val description p d R H B src f bank l mem)

local notation "owner" => scheduledCellOwner a D label assigned

/-- Read the arrays of the same sparse submission after transporting its
existential witness across a reached prefix. The native scanner's rows retain
both their candidate values and their original allocation shapes. -/
structure SparseReportSources.LocalReadback (geometry : ℕ → ℕ) (places : ℕ → CellPacket.Placed Site)
    (extra : ℕ → List CellSparse.Record) (submitted : ℕ → SparseExterior.Owned) {layout : ReportLayout}
    (atCell : Fin a.cells → ReportCell layout) (original sampled : List (ReportCell layout)) : Prop where
  /-- The selected scanner's native count and use field layout. -/
  layoutEq : S.layout=layout
  /-- Global placed sparse packets, before compaction by owner. -/
  placedEq : S.places=places
  /-- Addresses of the original public geometry. -/
  geometryEq : S.geometry=geometry
  /-- Exact emitted supplemental records. -/
  extraEq : S.extra=extra
  /-- Raw physical field proposal at every owned global ordinal. -/
  cellsEq : S.cells=submitted
  /-- All sampled report digits on the underlying uncompressed cell array. -/
  reportsEq : HEq S.reports atCell
  /-- The local scanner enumerates the same candidate sequence as the typed packets. -/
  sampledEq : HEq (S.reportRows (team:=team)) sampled
  /-- The original report allocation is valid on this exact selected array. -/
  same : HEq (eraseReportBits original) (eraseReportBits (S.reportRows (team:=team)))

/-- The charged scanner sees the increasing global-cell list produced by its
actual owner scan. Only the entries retained in this team enter the list. -/
theorem SparseReportSources.reportRows_scan (atCell : ℕ → ReportCell S.layout) (who : ℕ → ℕ)
    (names : ∀ c : Fin a.cells, who c.val=owner c)
    (rows : ∀ c, owner c=team.val → S.reports c=atCell c.val) :
    S.reportRows=((List.range a.cells).filter (fun c => decide (who c=team.val))).map atCell := by
  let ord := SparseExterior.programOrder l mem owner team.val S.cellCount S.teamID S.owners
  let ids := List.ofFn fun i : Fin (l.before mem l.cells) => globalCell l.toLayout mem i.val
  have same : S.reportRows=ids.map atCell := by
    simp only [SparseReportSources.reportRows,ids,List.map_ofFn,Function.comp_def]
    apply congrArg List.ofFn
    funext i
    exact (rows (ord i).val (ord i).property).trans (congrArg atCell
      (SparseExterior.programOrder_val l mem owner team.val S.cellCount S.teamID S.owners i))
  apply same.trans
  apply congrArg (List.map atCell)
  apply (globalCell_prefix l.toLayout mem l.cells le_rfl).trans
  rw [S.cellCount]
  apply List.filter_congr
  intro c hc
  have bound : c<a.cells := List.mem_range.mp hc
  rw [S.teamID,show l.owner mem c=who c from (S.owners ⟨c,bound⟩).trans (names ⟨c,bound⟩).symm]

/-- If the cell list of the charged native scan is a sampled version of the
returned physical source list, it uses that source's actual scanner input. -/
theorem SparseReportSources.preparedReports {buf : Memory w} {q : ReportCursor}
    (source : ℕ → ReportCell S.layout) (who : ℕ → ℕ) (names : ∀ c : Fin a.cells, who c.val=owner c)
    (cs : List (ReportCell S.layout)) (seed : PreparedReportInput pub buf cs q description)
    (picked : ∀ c, owner c=team.val → S.reports c=source c.val)
    (same : eraseReportBits cs=eraseReportBits (((List.range a.cells).filter (fun c => decide (who c=team.val))).map source)) :
    PreparedReportInput pub buf S.reportRows q description := by
  apply seed.of_same
  rw [S.reportRows_scan source who names picked]
  exact same

/-- On a genuine sampled cell list the four controls and all its candidate-
dependent inputs are those of the source scan, in its original global order. -/
theorem SparseReportSources.preparedAtLocalTapes {buf : Memory w} {q : ReportCursor}
    (source : ℕ → ReportCell S.layout) (who : ℕ → ℕ) (names : ∀ c : Fin a.cells, who c.val=owner c)
    (seed : PreparedReportInput pub buf (((List.range a.cells).filter (fun c => decide (who c=team.val))).map source) q description)
    (tape : ℕ → ℕ → Bool) (start : ℕ → ℕ)
    (picked : ∀ c, owner c=team.val → S.reports c=(source c.val).withTape (tape c.val) (start c.val)) :
    PreparedReportInput pub buf S.reportRows q description := by
  exact S.preparedReports (fun i => (source i).withTape (tape i) (start i)) who names _ seed picked
    (eraseReportBits_localTapes _ source tape start).symm

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
