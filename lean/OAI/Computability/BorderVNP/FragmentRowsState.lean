import OAI.Computability.BorderVNP.FragmentRows
import OAI.Computability.BorderVNP.PackedReportWriter

/-! # Register and memory specification for the three sparse input passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Each pass visits its source once, retaining the public order. -/
inductive Pass where
  | cable (side : Bool)
  | data

/-- Instruction sequence for processing one entry of the selected pass. -/
def Pass.step : Pass → Code
  | .cable side => cableStep side
  | .data => dataStep

/-- Register containing the upper bound of the selected traversal. -/
def Pass.boundReg : Pass → Reg
  | .cable _ => 7
  | .data => 9

/-- Number of source entries examined by this pass. -/
def Pass.count (l : Layout) : Pass → ℕ
  | .cable _ => l.host.count
  | .data => l.count

/-- Read a cable row on the selected side or a live data row at the given index. -/
def Pass.row (l : Layout) (m : ℕ → ℕ) : Pass → ℕ → Option Quad
  | .cable side => Diagonal.ExternalSew.Fragments.cable l.host m side
  | .data => l.liveRow m

/-- Stable configuration of the three loops. -/
def Layout.regValue (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7
  | 6 => l.host.cables | 7 => l.host.count | 8 => l.deliveries | 9 => l.count
  | 10 => l.host.relative | 11 => l.host.cells | 12 => l.control | 13 => l.quads
  | 16 => l.supplied | _ => 0

/-- The registers used by the three passes hold their layout-specified initial values. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop :=
  ∀ j : Reg, j.val ≤ 13 ∨ j.val = 16 → z.reg j = l.regValue j.val

/-- Each input word used in later iterations retains its original value. -/
def Layout.Frozen (l : Layout) (before m : ℕ → ℕ) : Prop := ∀ a, l.Input a → m a = before a

/-- Exact register and full memory result of emitting an optional quadruple. -/
def StepResult (l : Layout) (m : ℕ → ℕ) (i used : ℕ) (o : Option Quad) (z : NatState) : Prop :=
  l.Ready z ∧ z.reg 15 = i+1 ∧ z.reg 14 = used+o.toList.length ∧
    z.mem = Packing.BottomReports.Writer.write m (l.quads+4*used) (o.toList.flatMap Quad.words)

set_option maxHeartbeats 2000000 in
/-- The fixed entry initializes its registers directly from the same memory
whose cable and data words the passes subsequently use. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout)
    (layout : l = Layout.fromFrame (readings pub 0) (readings m)) (fit : l.Fits w (readings m)) :
    BoundedRun pub mac setup r m setup.slots (fun z => l.Ready z ∧ z.reg 14 = 0 ∧ z.mem = readings m) := by
  subst l
  let l := Layout.fromFrame (readings pub 0) (readings m)
  have head : readings pub 0 + 92 < 2^w := fit.head
  have ctl : readings m (readings pub 0+92)+29 < 2^w := fit.control
  have rel : readings m (readings pub 0+87)+2*readings m (readings pub 0+7) < 2^w :=
    (Nat.le_add_right l.supplied l.cells).trans_lt fit.relativeEnd
  have fs (d : Reg) (f : Word 8) (z : NatState) (h : f.val ≤ 92) :
      (readFrame d 62 63 f).fixedSafe w (readings pub) z := readFrame_fixedSafe d f _ z w (by omega)
  have hw : w ≠ 0 := by rintro rfl; norm_num at head
  have safe : setup.fixedSafe w (readings pub) (.ofWords r m) := by
    simp (config := {decide := true}) [setup,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,readFrame_fixedEval,NatState.ofWords,addressOpFits,addressOp,fs,hw]
    omega
  apply (setup.runFixed pub mac r m safe).mono le_rfl
  rintro z rfl
  refine ⟨?_,?_,?_⟩
  · intro j hj
    rcases j with ⟨j,hj'⟩
    change j ≤ 13 ∨ j = 16 at hj
    rcases hj with h|rfl
    · interval_cases j <;> simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,
        readFrame_fixedEval,Layout.regValue,Layout.fromFrame,Cube.HostScatter.Layout.fromFrame,
        NatState.ofWords,addressOp]
    · simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,readFrame_fixedEval,
        Layout.regValue,Layout.fromFrame,Layout.supplied,Cube.HostScatter.Layout.fromFrame,NatState.ofWords,addressOp]
  · simp (config := {decide := true}) [setup,Code.block,Code.fixedEval,Code.evalNat,readFrame_fixedEval,NatState.ofWords]
  · simp [setup,Code.block,Code.fixedEval,readFrame_fixedEval,NatState.ofWords]

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
