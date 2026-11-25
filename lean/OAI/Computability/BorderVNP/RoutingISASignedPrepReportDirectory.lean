import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation
import OAI.Computability.BorderVNP.DiagonalTallyReportDirectoryAllocation

/-! # Seeding the native report tape from the two physical owner directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports.ReportDirectory

open RoutingISA DiagonalTallyAllocation VPVNP.BurstRAM
open private published_read data_banks from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory

variable {w description : ℕ} {pub : Arg → Word w} {m : Memory w}
    {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {l : ReportLayout} {q : ReportCursor}
    (d : Packing.BundleDirectory.Layout) (rows : CellControlRows.Layout)
    (owner : Fin d.bundles → Fin d.cells) (source : Fin d.bundles → ReportBundle)
    (raw : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)

private theorem publishedSeed (bind : Bindings pre d rows l) (seed : l.seed q (raw (l.frame+90)) raw)
    (controlBefore : l.control+28 ≤ banks.bankStart) (controlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (frameBefore : l.frame+96 ≤ banks.bankStart) (bankBefore : banks.bankStart ≤ pre.start) :
    let middle := grouped d owner source raw
    let cs := directoryCells d rows l owner source middle counts
    l.seed q cs.length (rows.published middle) := by
  intro middle cs
  have cuts := data_banks d rows l bind
  have keep (a : ℕ) (ha : a<pre.start) (ne : a≠l.frame+90) : rows.published middle a=raw a := by
    rw [published_read _ _ _ (by simp only [CellControlRows.Layout.outputs,bind.frame]; omega)]
    exact d.image_outside _ raw d.cells a (.inl (by omega)) (.inl (by omega))
  have fr (j : ℕ) (hj : j<96) (hn : j≠90) := keep (l.frame+j) (by omega) (by omega)
  have ct (j : ℕ) (hj : j<28) := keep (l.control+j) (by omega) (by omega)
  obtain ⟨p92,_,p95,p81,p44,c17,c19,c22,c23,c24,c25,c26,c27⟩ := seed
  refine ⟨(fr 92 (by decide) (by decide)).trans p92,?_,(fr 95 (by decide) (by decide)).trans p95,
    (fr 81 (by decide) (by decide)).trans p81,(fr 44 (by decide) (by decide)).trans p44,
    (ct 17 (by decide)).trans c17,(ct 19 (by decide)).trans c19,(ct 22 (by decide)).trans c22,
    (ct 23 (by decide)).trans c23,(ct 24 (by decide)).trans c24,(ct 25 (by decide)).trans c25,
    (ct 26 (by decide)).trans c26,(ct 27 (by decide)).trans c27⟩
  simp [CellControlRows.Layout.published,bind.frame,cs,directoryCells]

/-- The original frame pointers and private site receipts give the native tape
bijection at the end of stable bundle grouping and compact owned-row publication.
Slot 90 is obtained from the actual number of owned cells at this return. -/
theorem preparedInput_owned (bind : Bindings pre d rows l) (fp : (pub 0).val=l.frame)
    (seed : l.seed q (raw (l.frame+90)) raw) (rowRoom : rows.Room w) (ctl : l.ScannerControls raw)
    (controlBefore : l.control+28 ≤ banks.bankStart) (controlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (∃ c∈directoryCells d rows l owner source (grouped d owner source raw) counts, (owner j).val=c.number) →
      (source j).delivered l description raw ∧ (source j).SiteRoom l w description)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets<2^w)
    (rawRoom : l.fieldWidth+l.bodyCap<2^w) (space : post.fresh<2^w) :
    let middle := grouped d owner source raw
    let cs := directoryCells d rows l owner source middle counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      (∀ c∈cs, c.privateWires+c.supplied+c.tailWidth<2^w) →
      readings m=rows.published middle → PreparedReportInput pub m cs q description := by
  intro middle cs alloc slots privateEnd image
  have data := physicalInput_owned d rows l owner source bind w description raw counts rowRoom ctl controlBefore
    controlFrame receipt alloc slots
  have ready := publishedSeed d rows owner source raw counts bind seed controlBefore controlFrame alloc.frameBefore
    (Nat.le_trans (Nat.le_add_right ..) alloc.bankBefore)
  exact alloc.preparedInput fp (image ▸ ready) (image ▸ data) slots controlBefore privateEnd width coords rawRoom space

/-- The seed also applies to a memory carrying the full site catalog. -/
theorem preparedInput (bind : Bindings pre d rows l) (fp : (pub 0).val=l.frame)
    (seed : l.seed q (raw (l.frame+90)) raw) (rowRoom : rows.Room w) (ctl : l.ScannerControls raw)
    (controlBefore : l.control+28 ≤ banks.bankStart) (controlFrame : l.control+28 ≤ l.frame ∨ l.frame+96 ≤ l.control)
    (receipt : ∀ j, (source j).delivered l description raw ∧ (source j).SiteRoom l w description)
    (width : l.fieldWidth ≤ w) (coords : l.parameters+l.gadgets<2^w)
    (rawRoom : l.fieldWidth+l.bodyCap<2^w) (space : post.fresh<2^w) :
    let middle := grouped d owner source raw
    let cs := directoryCells d rows l owner source middle counts
    ReportAllocation pre post banks l cs q → SiteIntervals cs description banks.stride →
      (∀ c∈cs, c.privateWires+c.supplied+c.tailWidth<2^w) →
      readings m=rows.published middle → PreparedReportInput pub m cs q description :=
  preparedInput_owned d rows owner source raw counts bind fp seed rowRoom ctl controlBefore controlFrame
    (fun j _ => receipt j) width coords rawRoom space

end DiagonalTallyCellReports.ReportDirectory

end BorderVNP
end Computability
end OAI
