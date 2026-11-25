import OAI.Computability.BorderVNP.CubeGroupNativeCheckedRun
import OAI.Computability.BorderVNP.CubeTeamOwnedScheduledWords

/-! # Capacity and scanner metadata on the actual checked schedule

The physical histogram, greedy owner writes and native capacity comparisons
all run on the memory returned by the minimum check. Their returning traces
supply both the scheduled arrays and the scanner's public operands.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open RoutingISA VPVNP.BurstRAM

/-- From an actual checked frame, the native schedule returns precisely when
the loads it computes meet the per-team and aggregate limits. -/
theorem checked_test_of_frame {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (wl : Layout) (tl : TeamNative.Layout) (X : ℕ)
    (base : readings pub 0 = wl.frame) (frame : CheckedFrame wl tl (readings m) w X)
    (sumFits : ∑ k ∈ Finset.range wl.groups, wl.weight (readings m) k < 2^w) :
    let budget : TeamBudget.Layout := ⟨tl.r+1,X,tl.totals⟩
    TestRun pub mac checkedSchedule r m
      (ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(tl.r+1)*(TeamBudget.row.slots+1)+1))
      ((∀ j, TeamNative.loads tl.r (wl.weight (readings m)) wl.groups j ≤ budget.teamLimit) ∧
        (∑ k ∈ Finset.range wl.groups, wl.weight (readings m) k) ≤ budget.totalLimit)
      (fun z => ScheduleResult wl tl (readings m) z.mem) := by
  intro budget
  have scheduled := run_schedule pub mac wl tl r m base frame.fields frame.setup frame.fits frame.allocated
    frame.frameFit frame.frame frame.groups frame.weights frame.keepAssign sumFits
  exact checked_test pub mac wl tl r m X scheduled budget rfl
    (base ▸ frame.budgetFields) (base ▸ frame.budgetFits) (base ▸ frame.keepBudget)

end Cube.GroupWeights

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical LocalRow CubeHeaderInstall TeamContraction.ProcessorSlots

/-- Every returning checked schedule produces its real greedy owner array and all
scanner words for this team. Conversely, meeting the two native capacity limits
gives an execution with these same outputs at the indicated clock bound. -/
theorem Layout.checkedScanner_test {w : ℕ} (a : Layout) (pub : Arg → Word w)
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    {bits : List Bool} {orig : Memory w}
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits orig)
    (decl : Broadcast a.n a.header.d a.header.cap)
    {bootRegs : Bank w} {bootMem : Memory w}
    (decoded : DecodedRows a (readings pub) f.dst decl (readings orig) (.ofWords bootRegs bootMem))
    {mac : TeamOpcode.Macros w 8} {es minRegs minMem}
    (minimum : Runs pub mac CubeLengths.minimum bootRegs bootMem es minRegs minMem)
    (wl : GroupWeights.Layout) (tl : TeamNative.Layout) (X : ℕ)
    (base : readings pub 0 = wl.frame) (frame : GroupWeights.CheckedFrame wl tl (readings minMem) w X)
    (sumFits : ∑ k ∈ Finset.range wl.groups, wl.weight (readings minMem) k < 2^w)
    (groups : wl.groups = a.header.d) (weights : wl.weights = a.groupWeights)
    (totals : tl.totals = a.teamTotals) (owners : tl.owners = a.ownerBase)
    (axes : a.header.a = a.n+1) (primary : (pub 0).val+112 ≤ a.header.header)
    (positive : 0 < a.header.d) (stopFit : a.stop < 2^w) (labelsFit : a.alphabet < 2^w) :
    let budget : TeamBudget.Layout := ⟨tl.r+1,X,tl.totals⟩
    TestRun pub mac GroupWeights.checkedSchedule minRegs minMem
      (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(tl.r+1)*(TeamBudget.row.slots+1)+1))
      ((∀ j, TeamNative.loads tl.r (wl.weight (readings minMem)) wl.groups j ≤ budget.teamLimit) ∧
        (∑ k ∈ Finset.range wl.groups, wl.weight (readings minMem) k) ≤ budget.totalLimit)
      (fun z => GroupWeights.ScheduleResult wl tl (readings minMem) z.mem ∧
        a.ScannerWords (readings pub 0) f.team (readCode (a.n+1) decl.1)
          (fun g => (TeamNative.owner tl.r (wl.weight (readings minMem)) g.val).val)
          (readings pub) z.mem (fun p j => readCode (a.header.cap+1) (decl.2 p j))) := by
  intro budget
  apply (GroupWeights.checked_test_of_frame pub mac minRegs minMem wl tl X base frame sumFits).mono le_rfl Iff.rfl
  exact fun z hz => ⟨hz,a.scannerWords_of_schedule pub f old fresh profile gates outputs width off ell
    pins decl decoded minimum wl tl hz groups weights totals owners axes primary positive stopFit labelsFit⟩

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
