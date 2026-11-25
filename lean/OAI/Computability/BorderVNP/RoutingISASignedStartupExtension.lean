import OAI.Computability.BorderVNP.RoutingISASignedFrame
import OAI.Computability.BorderVNP.CubeISAHeaderInstallExtension

/-! # The same 81 startup words for the signed tasks, geometric packet and cube -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction.ProcessorSlots GeometryAdvice

variable {w : ℕ} (l : Layout) (raw team subtotal : ℕ) (old : Fin 81 → Word w)

/-- Every statically selected cube word is already installed in the signed task
frame. The other positions retain their actual signed and residue operands. -/
theorem Layout.cube_extension_signed :
    l.cube.extension (l.extension raw team subtotal old) = l.extension raw team subtotal old := by
  funext i
  by_cases selected : l.cube.operand (31+i.val) = none
  · exact l.cube.extension_other _ i selected
  · have separate : 31+i.val ∉ ([33,34,35,36,38,39,40,44,45,46,71,80,89,90,95] : List ℕ) := by
      intro h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> exact selected (by rw [h]; rfl)
    rw [l.extension_cube raw team subtotal old i separate]
    simp only [CubeArena.Layout.extension]
    cases h : l.cube.operand (31+i.val) with
    | none => exact (selected h).elim
    | some _ => rfl

private theorem sameWord (v : Word w) : TeamTapeInputEmit.word w v.val = v :=
  Fin.ext (Nat.mod_eq_of_lt v.isLt)

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
/-- Writing the seven bootstrap scalars and eleven geometry words before or
after the signed task operands gives the identical literal read by the processor. -/
theorem Layout.extension_joint (fresh profile gates outputs width off ell d n blocks b h s : ℕ) :
    CubeHeaderInstall.jointFields (l.extension raw team subtotal old) fresh profile gates outputs width off ell d n blocks b h s =
      l.extension raw team subtotal (CubeHeaderInstall.jointFields old fresh profile gates outputs width off ell d n blocks b h s) := by
  funext i
  fin_cases i <;> first | rfl | exact (sameWord _).symm

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
