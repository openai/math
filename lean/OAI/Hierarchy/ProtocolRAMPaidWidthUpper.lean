import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Upper frame for the paid-width sparse scatter and its original scratch tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open scoped Fin.CommRing
variable {W edges : ℕ}

theorem Slice.above (s : Slice) (bank : Bank) (edges src : ℕ) (m : Memory W)
    (fit : s.Fits bank edges src W) (x : ℕ) (bankEnd : bank.base+edges<x)
    (scratchEnd : src+2*s.count≤x) : s.Out bank edges src m x=m x := by
  have left:=fit.bound
  have right:=fit.room
  unfold Out RepairHistogram.result
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by
    intro i
    rw [s.address_eq bank m i edges (by omega)]
    have := min_le_right (s.edge.eval m (i.val:Word W)).val edges
    omega)]
  exact ProtocolRAMGeneratedWrite.frame_image src (2*s.count) _ m x (.inr scratchEnd)

theorem applyAll_above (bank : Bank) (edges src : ℕ) (ss : List Slice) (m : Memory W) (x : ℕ)
    (fit : ∀s∈ss,s.Fits bank edges src W) (bankEnd : bank.base+edges<x)
    (scratchEnd : ∀s∈ss,src+2*s.count≤x) : applyAll bank edges src ss m x=m x := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    exact (ih _ (fun t ht=>fit t (List.mem_cons_of_mem _ ht))
      (fun t ht=>scratchEnd t (List.mem_cons_of_mem _ ht))).trans
      (s.above bank edges src m (fit s List.mem_cons_self) x bankEnd (scratchEnd s List.mem_cons_self))

theorem output_above (bank : Bank) (edges src : ℕ) (ss : List Slice) (m : Memory W) (x : ℕ)
    (fit : ∀s∈ss,s.Fits bank edges src W) (bankEnd : bank.base+edges<x)
    (scratchEnd : ∀s∈ss,src+2*s.count≤x) : output bank edges src ss m x=m x :=
  (applyAll_above bank edges src ss _ x fit bankEnd scratchEnd).trans
    (ProtocolRAMGeneratedWrite.frame_image bank.base edges (.lit 0) m x (.inr bankEnd.le))

end Hierarchy.ProtocolRAM.PaidWidths
end

end OAI
