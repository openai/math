import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.FiniteEvaluatorReportedFragmentInput

/-! # Retained fragment tables on the signed report return

The assigned cell reports can change primary word 35. The host pointers and
all the fields used by the fragment emitter survive every report choice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM BorderVNP.Cube FiniteEvaluator Evaluator Evaluator.ScheduleClock
open DiagonalTallyAllocation DiagonalTallyCellReports

variable {w team offsets ctl live ports bundles b description : ℕ} (a : Layout)
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {entry : Memory w}
    {initial written : ℕ → ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "H" => a.openInputs team (pub 0).val offsets ctl live ports bundles b owner header

/-- The signed reporter preserves the four read tables and physical host-bank
pointers of the fragment program even when every sampled report bit is arbitrary. -/
theorem Layout.signed_report_words {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {banks : CellBanks.Layout} (opened : Returns Evaluator.SignedPrep.controls pub mac bank entry)
    (reported : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (seed : PreparedReportInput pub opened.val.2.2 cs q description)
    (keep : CubeAllocation.HostRetention a.cube frame initial written (readings entry))
    (ready : OpenSuffix.Ready H frame (readings entry) w)
    (position : OpenSuffix.Placement H a.cube a.before frame (readings entry))
    (allocation : ReportAllocation a.before a.after banks l cs q) (start : banks.bankStart=a.cube.cellBank) :
    ReportWords a frame initial written (readings reported.val.2.2) true := by
  have openedImage := ((OpenSuffix.run H ready).sound opened.property).2
  have low (x : ℕ) (before : x<a.cube.cellBank) (n35 : x≠frame+35) (n90 : x≠frame+90) :
      readings reported.val.2.2 x=readings entry x := by
    have stayed := report_return_before_cells seed allocation reported (x:=x) (start ▸ before)
      (seed.framePointer ▸ n35)
    exact (congrArg Fin.val stayed).trans ((congrFun openedImage x).trans (a.open_image_low owner header position x before n90))
  refine ⟨keep.primary,?_,?_⟩
  · intro x hx n13 n46 n90 n35
    exact (low x (hx.trans_le a.open_table_order.1) (n35 rfl) n90).trans (keep.lower x hx n13 n46)
  · intro c hc
    obtain ⟨first,pubEnd,link,ownerEnd,pairEnd,hostEnd,_,_⟩ := a.cube.writer_order
    have below := a.open_table_order
    have primary := keep.primary
    have whole : a.cube.publicBase ≤ a.cube.hostDirectory+c*2+1 ∧ a.cube.hostDirectory+c*2+1 < a.cube.records := by omega
    exact (low _ (by omega) (by omega) (by omega)).trans (keep.tables _ whole.1 whole.2)

/-- The emitter's raw row count is the length of the compacted public
directory, including on a signed report that overwrites primary word 35. -/
theorem ReportWords.compacted_count {a : Layout} {wordBase raw : ℕ} {placed : Memory w}
    {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {result written : ℕ → ℕ} {signed : Bool}
    (h : ReportWords a wordBase (readings (Packing.Directory.ISA.publish placed wordBase raw (dir.directory pp lp))) written result signed)
    (fit : (dir.directory pp lp).length < 2^w) :
    (FragmentRows.Layout.fromFrame wordBase result).count=(dir.directory pp lp).length := by
  change result (wordBase+9)=_
  rw [h.frame_word 9 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)]
  change (Packing.Directory.ISA.publish placed wordBase raw (dir.directory pp lp) (wordBase+9)).val=_
  rw [Packing.Directory.ISA.publish,Function.update_self]
  exact Nat.mod_eq_of_lt fit

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
