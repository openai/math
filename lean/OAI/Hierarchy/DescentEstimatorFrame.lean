import OAI.Hierarchy.DescentCanvasFrameBasics
import OAI.Hierarchy.DescentEstimatorCalendarFrame
import OAI.Hierarchy.DescentEstimatorAny
import OAI.Hierarchy.DescentEstimatorArenaExtent
import OAI.Hierarchy.DescentGLPhysicalFrame

namespace OAI
/-! # Mutable addresses of the complete installed estimator on arbitrary incoming data -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentGL ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ} (E : EstimatorArena)

theorem spectrum_frame (m : Memory w) (a : ℕ) (away : a<E.start ∨ E.inputEnd≤a) :
    E.spectrumMem m a=m a := by
  let top:=sqOffset E.start E.hosts E.high E.low
  have lo : E.start+(E.dim+1)*page E.hosts E.high=top:=rfl
  have endAt : top+(E.dim+1)*page E.hosts E.high=E.inputEnd := by
    unfold inputEnd numeratorAt location
    rw [Nat.add_mul,Nat.one_mul,Nat.add_assoc]
  have pitch:=rows_le E.hosts E.high
  have margin:=Nat.mul_le_mul_right (page E.hosts E.high) (show 1≤E.dim+1 by omega)
  rw [Nat.one_mul] at margin
  unfold spectrumMem numeratorMem
  apply (after_frame E.transformAt top E.hosts E.high E.low E.precision _ a (by change a<top ∨ top+(E.dim+1)*_≤a;omega)).trans
  apply (ProtocolRAMGeneratedWrite.frame_image top _ _ _ a (by omega)).trans
  exact after_frame _ _ _ _ _ _ _ a (by change a<E.start ∨ E.start+(E.dim+1)*_≤a;omega)

theorem any_frame (fit : E.Fits w) (m : Memory w) (a : ℕ) (outside : a<E.origin ∨ E.endAddress≤a) :
    E.image (E.literal m) a=m a := by
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇⟩:=E.areas
  have static:E.origin≤E.staticEnd:=(a₁.trans (a₂.trans (a₃.trans a₄))).trans (Nat.le_add_right ..)
  have start:E.staticEnd≤E.start:=Nat.le_add_right ..
  have gap:E.start≤E.inputEnd:=a₆.trans (Nat.le_add_right ..)
  have before:E.inputEnd≤E.solveAt:=Nat.le_add_right ..
  have last : E.solveAt≤E.endAddress := by
    have data : E.solveAt≤PhysicalTrajectory.outputBase E.dim E.solveAt :=
      (Nat.le_add_right E.solveAt (E.dim*(3*2^E.dim+1))).trans (Nat.le_add_right _ (2^E.dim))
    exact data.trans (Nat.le_add_right _ (2^E.dim))
  apply (PhysicalTrajectory.final_frame E.dim E.solveAt E.bank _ a (by change a<E.solveAt ∨ E.endAddress≤a;omega)).trans
  apply (E.calendar_frame fit _ a (by omega)).trans
  apply (E.spectrum_frame _ a (by omega)).trans
  rcases outside with h|h
  · exact E.literal_before m h
  · exact E.literal_after m (by omega)

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
