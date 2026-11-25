import OAI.Computability.BorderVNP.DiagonalPreparedBundleRows
import OAI.Computability.BorderVNP.DiagonalSignedNativePacketSeeds

/-! # The emitted supplemental fields at an actual owned report visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA TypedTaskBuilder CellSparse
open private bundleCursor_tape from OAI.Computability.BorderVNP.RoutingISAScheduleClockReports

variable {l : ReportLayout} (rows : CellControlRows.Layout) (raw : ℕ → ℕ) (atCell : ℕ → ReportCell l)
    (q : ReportCursor)

local notation3 (prettyPrint := false) "cs" => visitedReportRows rows raw atCell

/-- The local supplemental cursor reflects all preceding owned report writes. -/
noncomputable def visitedLocalCursor (c : ℕ) : LocalReportCursor :=
  (atCell c).localStart (previousReportCursor cs q (rows.before raw c))

/-- The actual original-bundle read follows the count writer at this local row. -/
noncomputable def visitedBundleMemory {w : ℕ} (buf : Memory w) (c : ℕ) : ℕ → ℕ :=
  let i := rows.before raw c
  ((atCell c).countFrame (previousReportCursor cs q i)).image .count (previousReportMemory cs q (readings buf) i)

/-- Genuine numbered rows of the owner scan cannot repeat, and the readback
of their global number recovers the exact prefix index. -/
theorem visitedReportRows_rank (numbers : ∀ c, (atCell c).number=c) (j : Fin (cs).length) :
    rows.before raw ((cs).get j).number=j.val := by
  have range : j.val<rows.before raw rows.cells := by
    simpa only [visitedReportRows,List.length_ofFn] using j.isLt
  let i : Fin (rows.before raw rows.cells) := ⟨j.val,range⟩
  have keep : (cs).get j=atCell (globalCell rows.toLayout raw i.val) := by
    change (List.ofFn _).get j=_
    exact List.get_ofFn _ j
  rw [keep,numbers]
  exact (global_spec rows.toLayout raw range).2.2

/-- The canonical supplemental array emitted by the signed task patch contains
the records of this same local selected report and its true preceding cursor. -/
theorem visited_seedExtras (numbers : ∀ c, (atCell c).number=c)
    (c : ℕ) (bound : c<rows.cells) (owned : rows.owner raw c=rows.team) :
    seedExtras cs q c = bindingRows (atCell c).bundles (visitedLocalCursor rows raw atCell q c) := by
  classical
  obtain ⟨i,rank,selected⟩ := visitedReportRows_owned rows raw atCell c bound owned
  have hit : ∃ j : Fin (cs).length, (cs)[j].number=c :=
    ⟨i, (congrArg ReportCell.number selected).trans (numbers c)⟩
  let j := Classical.choose hit
  have name : ((cs).get j).number=c := Classical.choose_spec hit
  have before := visitedReportRows_rank rows raw atCell numbers j
  rw [name] at before
  have same : j=i := Fin.ext (before.symm.trans rank.symm)
  rw [seedExtras,dite_eq_left hit]
  change bindingRows ((cs).get j).bundles (((cs).get j).localStart (previousReportCursor cs q j.val))=_
  rw [same,selected,rank]
  rfl

/-- Overwriting count and use bits keeps every preceding native cursor. The
offset of each row may be taken from the actual local chronological stream. -/
theorem previousReportCursor_sampled (tape : ℕ → Bool) (position : ℕ → ℕ) (i : ℕ) :
    previousReportCursor (visitedReportRows rows raw (fun c => (atCell c).withTape tape (position c))) q i =
      previousReportCursor cs q i := by
  have fold (ids : List ℕ) (initial : ReportCursor) :
      (ids.map (fun c => (atCell c).withTape tape (position c))).foldl (fun a r => r.after a) initial =
        (ids.map atCell).foldl (fun a r => r.after a) initial := by
    induction ids generalizing initial with
    | nil => rfl
    | cons c ids ih =>
      have after : ((atCell c).withTape tape (position c)).after initial=(atCell c).after initial := bundleCursor_tape ..
      simp only [List.map_cons,List.foldl_cons,after,ih]
  simp only [previousReportCursor,visitedReportRows_scan,←List.map_take]
  exact fold _ _

/-- The selected task patch can use the author's original unfilled report rows.
Each proposed native assignment gives the same exact typed record stream and
local supplemental addresses on its owned cells. -/
theorem visited_seedExtras_sampled (numbers : ∀ c, (atCell c).number=c)
    (tape : ℕ → Bool) (position : ℕ → ℕ) (c : ℕ) (bound : c<rows.cells) (owned : rows.owner raw c=rows.team) :
    let sampled := fun k => (atCell k).withTape tape (position k)
    seedExtras cs q c = bindingRows (sampled c).bundles (visitedLocalCursor rows raw sampled q c) := by
  intro sampled
  rw [visited_seedExtras rows raw atCell q numbers c bound owned]
  unfold visitedLocalCursor
  rw [previousReportCursor_sampled rows raw atCell q tape position]
  exact (bindingRows_tapeBundles ..).symm

/-- Replacing only the report digits transfers the real native scanner input to
the original ownership order of this compact call. -/
theorem PreparedReportInput.visitedSource {w description : ℕ} {pub : Arg → Word w} {buf : Memory w}
    (source : ℕ → ReportCell l)
    (seed : PreparedReportInput pub buf
      (((List.range rows.cells).filter (fun c => decide (rows.owner raw c=rows.team))).map source) q description)
    (tape : ℕ → Bool) (position : ℕ → ℕ) :
    PreparedReportInput pub buf
      (visitedReportRows rows raw (fun c => (source c).withTape tape (position c))) q description := by
  apply seed.of_same
  rw [visitedReportRows_scan]
  exact (eraseReportBits_localTapes _ source (fun _ => tape) position).symm

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
