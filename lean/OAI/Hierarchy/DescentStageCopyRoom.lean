import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentPrivateClockScale

namespace OAI
/-! # Address bits of the original stack of copies -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler
variable {F:Type} [Field F] (G:PoweredGadget F)

/-- The copy count at the genuine growing residual group has a fixed linear
address width even when its dyadic exponent varies with the stage. -/
theorem stage_copies_word (t J f g reset M tail τ h : ℕ) (hh : 0<h)
    (age : (J+1)^2≤h) (reserve : tail≤τ*h) :
    (stageNumbers G t J f g reset M tail).copies≤
      2^((τ+privateGroupRate t (hostRate t reset) (capRate G t g) (cutRate t f g))*h) := by
  let c:=hostRate t reset
  let e:=capRate G t g
  let f₀:=cutRate t f g
  change 2^tail*(2^groupBits t J c e f₀)^((t+1)*J+1)≤_
  rw [←pow_mul,←pow_add]
  have inner := private_copy_bits t J c e f₀ 0 h hh age
  simp only [Nat.zero_add] at inner
  rw [Nat.add_mul τ (privateGroupRate t c e f₀) h]
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add reserve inner)

end Hierarchy.DescentSixParty.NativeBranch

end OAI
