import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.DiagonalSourceReturnedInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOwnedOpen
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenProfile

/-! # The occupied fragment frame on the signed report return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM _root_.OAI.Computability.BorderVNP.Cube FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports ScheduleClock
open SignedTaskArena

variable {w team offsets ctl live ports bundles b description : ℕ} (sa : SignedTaskArena.Layout)
    (owner : Fin bundles → Fin sa.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank : Bank w} {entry : Memory w}
    {initial written : ℕ → ℕ}
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "H" => sa.openInputs team (pub 0).val offsets ctl live ports bundles b owner header

/-- The signed report changes its descriptor counter and cell banks. The
fragment launcher reads its five header fields and all thirty-seven controls
from the original fitted public profile. -/
theorem ReportArgumentCut.header_from_profile {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {banks : CellBanks.Layout} {src : ReportAssignments cs}
    (opened : Returns controls pub mac bank entry)
    (report : Returns prepareCellReports pub mac opened.val.2.1 opened.val.2.2)
    (cut : ReportArgumentCut report src q description)
    (keep : CubeAllocation.HostRetention sa.cube frame initial written (readings entry))
    (ready : OpenSuffix.Ready H frame (readings entry) w)
    (position : OpenSuffix.Placement H sa.cube sa.before frame (readings entry))
    (allocation : ReportAllocation sa.before sa.after banks l cs q) (start : banks.bankStart=sa.cube.cellBank)
    (before : frame+112 ≤ ctl) (last : ctl+37 ≤ sa.cube.header.header)
    (fields : sa.OpenFields team frame offsets ctl live ports bundles initial)
    (words : ∀ i : Fin 37, initial (ctl+i.val)=sa.controls i.val)
    (entries : initial (frame+9) ≤ sa.cube.maxRows) (cells : initial (frame+11)=sa.cube.cells) :
    let raw := readings report.val.2.2
    (FragmentRows.Layout.fromFrame frame raw).Fits w raw ∧ raw (frame+92)=ctl ∧
      (∀ i : Fin 37, raw (ctl+i.val)=sa.controls i.val) ∧
      (FragmentRows.Layout.fromFrame frame raw).host.count=sa.cube.cables ∧
      raw (frame+9) ≤ sa.cube.maxRows ∧ raw (frame+11)=sa.cube.cells := by
  intro raw
  have openImage := ((OpenSuffix.run H ready).sound opened.property).2
  have frameID : l.frame=frame := cut.seed.framePointer.symm
  have read (x : ℕ) (low : x<sa.cube.header.header) (n13 : x≠frame+13) (n35 : x≠frame+35)
      (n46 : x≠frame+46) (n90 : x≠frame+90) : raw x=initial x := by
    have small := low.trans_le sa.open_table_order.1
    have stayed := report_return_before_cells cut.seed allocation report (x:=x) (start ▸ small) (frameID ▸ n35)
    exact (congrArg Fin.val stayed).trans ((congrFun openImage x).trans
      ((sa.open_image_low owner header position x small n90).trans (keep.lower x low n13 n46)))
  have primary := keep.primary
  refine ⟨cut.fragment_fit, (read (frame+92) (by omega) (by omega) (by omega) (by omega) (by omega)).trans fields.controlWord,
    fun i => ?_,(read (frame+7) (by omega) (by omega) (by omega) (by omega) (by omega)).trans fields.cables,
    (read (frame+9) (by omega) (by omega) (by omega) (by omega) (by omega)).trans_le entries,
    (read (frame+11) (by omega) (by omega) (by omega) (by omega) (by omega)).trans cells⟩
  have := i.isLt
  exact (read (ctl+i.val) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (words i)

/-- The two remaining fragment-row header fields come from the literal
published sparse-directory length and the geometry header on this boot. -/
theorem published_fragment_counts {axis : Fin (sa.cube.n+1)} {R origin raw : ℕ}
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (placed : Memory w)
    (base : ℕ) {input output : ℕ → ℕ}
    (entry : NativeEntry sa.cube base ctl axis R input
      (readings (Packing.Directory.ISA.publish placed base raw (dir.directory pp lp))) output)
    (primary : base+112 ≤ sa.cube.header.header)
    (hdr : Packing.RoutingOutputs.Header base origin sa.cube.cables sa.cube.cells dir.entries
      (readings (Packing.Directory.ISA.publish placed base raw (dir.directory pp lp))))
    (capacity : (dir.directory pp lp).length ≤ sa.cube.maxRows) :
    output (base+9) ≤ sa.cube.maxRows ∧ output (base+11)=sa.cube.cells := by
  have count := entry.low (base+9) (by omega)
  have cells := entry.low (base+11) (by omega)
  refine ⟨count.trans_le ?_,cells.trans hdr.cells⟩
  change (Packing.Directory.ISA.publish placed base raw (dir.directory pp lp) (base+9)).val ≤ _
  rw [Packing.Directory.ISA.publish,Function.update_self]
  exact (Nat.mod_le ..).trans capacity

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
