import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterResourcesWork
import OAI.Computability.VPVNP.LivePublicExpr

/-!
# The auxiliary verifier's private clock as a width-only operand

At the paper's word widths the parser clock dominates the assembler's
address-scan clock. The exact clock used by the native coefficient counter
can therefore be computed inside a virtual leaf from its word width alone.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM PrimedInputRAM LiveProgram

/-- Public operand computing the auxiliary coefficient verifier's instruction allowance as
twelve times the virtual word width plus 110. -/
def virtualFuel : PublicExpr := .add (.mul (.lit 12) .w) (.lit 110)

theorem virtualFuel_eval (g : Geometry) : virtualFuel.eval g = 12*g.w+110 := rfl

private theorem width_dominates (r : ℕ) : Opcodes.nativeFuel r+20 ≤ 12*(r+10)^4+110 := by
  have hs := Nat.pow_le_pow_right (by omega : 0 < r+10) (by decide : 2 ≤ 4)
  rw [pow_two] at hs
  unfold Opcodes.nativeFuel
  nlinarith [Nat.zero_le (r*r)]

theorem Data.fuel_eq_virtualFuel {n r H s : ℕ} {L : Lengths}
    {Q : Layout L n r H ((r+10)^4)} (D : Data Q s) (g : Geometry) (hw : g.w = (r+10)^4) :
    D.fuel = virtualFuel.eval g := by
  rw [virtualFuel_eval,hw]
  exact max_eq_right (width_dominates r)

private theorem fitsWidth (w : ℕ) (hw : 9 ≤ w) : 12*w+110 < 2^w := by
  induction w, hw using Nat.le_induction with
  | base => decide
  | succ w _ ih => rw [pow_succ]; omega

theorem virtualFuel_fits (g : Geometry) (hw : 9 ≤ g.w) : virtualFuel.Fits g (2^g.w) := by
  have h := fitsWidth g.w hw
  simp only [virtualFuel, PublicExpr.Fits, PublicExpr.eval, and_true]
  omega

theorem eventually_virtualFuel_cap (B : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, 6*(12*CursorBounds.wordBits B n+110) ≤ n^10 := by
  filter_upwards [Resources.eventually_privateWork B] with n h
  exact (Nat.mul_le_mul_left 6 (le_max_right _ _)).trans h

end PrimedCounter

end VPVNP
end Computability
end OAI
