import OAI.Computability.VPVNP.SliceArithmeticAccumulatePorts
import OAI.Computability.VPVNP.SliceArithmeticMultiplyCall
import OAI.Computability.VPVNP.SliceArithmeticAddCall

/-!
# A clean multiply-and-add call on extension-field coefficients

This subroutine adds the product of the two saved factors to the accumulator.
The caller supplies all three in the low-degree-first polynomial basis.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyAccumulate

open RAMTape
open SliceArithmeticRound (packed)

/-- One finite control copies the factors, multiplies and adds. -/
def machine : FiniteRoutine Port :=
  (stage.followedBy (MultiplyCall.machine.onPorts multiplyPorts)).followedBy (AddCall.machine.onPorts addPorts)

/-- Step bound for copying two packed factors, multiplying them, and adding the product to the
accumulator. -/
def callCap (e w : ℕ) := (10 * (e * w) + 4) + MultiplyCall.callCap e w + AddCall.callCap e w

/-- Both operands and the field advice are preserved, and the private
workspace is empty again when the updated accumulator returns. -/
theorem machine_runs {p e w : ℕ} [NeZero p] (he : 0 < e) (hw : Word.workingWidth p ≤ w)
    (c left returned acc : Vector p e) :
    let bits := fun v : Vector p e => packed w (List.ofFn v)
    ∃ t ≤ callCap e w, machine.Runs t
      (clean (external p e w (bits c) (bits left) (bits returned) (bits acc)))
      (clean (external p e w (bits c) (bits left) (bits returned) (bits (add acc (mul c left returned))))) := by
  intro bits
  let io := external p e w (bits c) (bits left) (bits returned) (bits acc)
  have copied := stage_runs io
  have hleft : (io .left).length = e*w := by simp [io, external, bits]
  have hreturned : (io .returned).length = e*w := by simp [io, external, bits]
  rw [hleft, hreturned] at copied
  obtain ⟨t₁, h₁, hr₁⟩ := MultiplyCall.machine_runs he hw c left returned
  have product := multiplyRun (bits c) (bits left) (bits returned) (bits acc) (bits (mul c left returned)) hr₁
  obtain ⟨t₂, h₂, hr₂⟩ := AddCall.machine_runs hw acc (mul c left returned) (bits c)
  have sum := addRun (bits c) (bits left) (bits returned) (bits acc) (bits (mul c left returned))
    (bits (add acc (mul c left returned))) hr₂
  exact ⟨_, by unfold callCap; omega, (copied.followedBy product).followedBy sum⟩

/-- A polynomial bound in the extension degree and working limb width. -/
theorem callCap_le (e w : ℕ) : callCap e w ≤ 3000 * (e + 1) ^ 2 * (w + 1) ^ 2 := by
  unfold callCap MultiplyCall.callCap HornerControl.digitCap AddCall.callCap
  ring_nf
  omega

end SliceArithmetic.MultiplyAccumulate

end VPVNP
end Computability
end OAI
