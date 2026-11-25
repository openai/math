import OAI.Hierarchy.DescentFallbackOperandBranch
import OAI.Hierarchy.DescentTreeLaneAddresses
import OAI.Hierarchy.DescentLaneCover

namespace OAI
/-! # Physical bit offsets and packed-word bounds for a measured fallback lane -/
namespace Hierarchy.DescentMeasuredFallbackLaneClock
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRouterSlots DescentContactTree DescentResetGates
open DescentOrderedReset DescentOrderedWords DescentTreeGateRefs DescentTreeLaneProgram
open DescentFallbackOperandBranch
open scoped Classical
noncomputable section

/-- The start field in the physical register counts bits. Dividing by the bundle
width gives the stored word index, including the last partial two-word range. -/
theorem lane_clock {Q I : Type} [Fintype I] {n p : ℕ} {width : Q→ℕ} (C : Config)
    (items : Fin C.count→DescentFallbackItemSelect.Item) (live : Finset (Fin C.count))
    (j : Fin C.count) (node : ℕ) (ids : I↪Fin n) (i : I) (b : Fin C.batches)
    (lane : DescentLaneGates.Lane p width) (units : Q→ℕ) (positive : 0<p)
    (earlier : DescentFallbackItemSelect.rank items live j=(before ids i).card)
    (phase : node%C.batches=b.val)
    (start : lane.start=batchStart ids i C.batches p b) (stride : lane.stride=1)
    (capacity : units lane.port=live.card*C.batches) :
    lane.start=C.startWord items live j node*p ∧
      lane.bundleStart=C.startWord items live j node ∧
      lane.count units=C.visibleWords items live j node := by
  have bits : lane.start=C.startWord items live j node*p := by
    rw [start,batchStart,Config.startWord,earlier,phase,Nat.add_mul,Nat.mul_assoc]
  have words : lane.bundleStart=C.startWord items live j node := by
    change lane.start/p=_
    rw [bits,Nat.mul_div_cancel _ positive]
  refine ⟨bits,words,?_⟩
  simp only [DescentLaneGates.Lane.count,Config.visibleWords,stride,capacity,words]

end
end Hierarchy.DescentMeasuredFallbackLaneClock

end OAI
