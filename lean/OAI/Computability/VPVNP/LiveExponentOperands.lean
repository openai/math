import OAI.Computability.VPVNP.LiveExponentFrame
import OAI.Computability.VPVNP.LiveProgramLayout
import Mathlib.Data.Fin.VecNotation

/-!
# Public operands of the live exponent table

These five expressions are evaluated from the processor's public geometry.
The header scan and the pair subroutine refer to the very same bit and
counter buffers. The stage dispatcher sits below the header workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.ExponentStage

open BurstRAM LiveHeaderWidths LiveExponent

/-- Public expressions for the incoming and outgoing digit arrays, increment counters, digit
width, and total digit count. -/
def operands (c : Constants) : Fin 5 → PublicExpr :=
  ![HeaderLayout.exponent c.lengths Layout.header .left,
    HeaderLayout.exponent c.lengths Layout.header .right,
    Layout.counter c, c.Z, c.labels*c.Z]

/-- Evaluate the exponent stage's five public address and size expressions as machine words for
the supplied geometry. -/
def words (c : Constants) (g : Geometry) : Fin 5 → Word g.w :=
  fun i => Fin.ofNat _ ((operands c i).eval g)

private theorem ranges (c : Constants) (g : Geometry) :
    let t := c.labels.eval g
    let Z := c.Z.eval g
    ((operands c 0).eval g + t*Z ≤ (Layout.counter c).eval g) ∧
    ((operands c 1).eval g + t*Z ≤ (Layout.counter c).eval g) ∧
    Layout.stageTag.eval g < (Layout.counter c).eval g := by
  dsimp only
  simp [operands, Layout.counter, Layout.descriptor, Layout.header, HeaderLayout.limit, HeaderLayout.config,
    HeaderLayout.exponent, HeaderLayout.exterior, HeaderLayout.advice, HeaderLayout.rightIndex,
    HeaderLayout.leftIndex, HeaderLayout.population, HeaderLayout.high, HeaderLayout.index, Constants.lengths,
    show (21 : PublicExpr).eval g = 21 from rfl]
  omega

theorem layout (c : Constants) (g : Geometry)
    (fit : (Layout.oldState c).eval g ≤ 2^g.w) (hasLabels : 0 < c.labels.eval g) :
    BufferLayout (words c g) (c.labels.eval g) (c.Z.eval g) := by
  obtain ⟨hl, hr, htag⟩ := ranges c g
  change (Layout.counter c).eval g + c.labels.eval g ≤ 2^g.w at fit
  have hc : (Layout.counter c).eval g < 2^g.w := by omega
  have hlen : c.labels.eval g*c.Z.eval g < 2^g.w := by omega
  have hwidth : c.Z.eval g < 2^g.w :=
    (Nat.le_mul_of_pos_left _ hasLabels).trans_lt hlen
  have hi : (operands c 0).eval g < 2^g.w := by omega
  have ho : (operands c 1).eval g < 2^g.w := by omega
  apply layout_of_ranges
  · exact Nat.mod_eq_of_lt hwidth
  · exact Nat.mod_eq_of_lt hlen
  · change (operands c 0).eval g % (2^g.w) + _ ≤ (Layout.counter c).eval g % (2^g.w)
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hc]
  · change (operands c 1).eval g % (2^g.w) + _ ≤ (Layout.counter c).eval g % (2^g.w)
    rwa [Nat.mod_eq_of_lt ho, Nat.mod_eq_of_lt hc]
  · change (Layout.counter c).eval g % (2^g.w) + c.labels.eval g ≤ 2^g.w
    rwa [Nat.mod_eq_of_lt hc]

theorem tag_fresh (c : Constants) (g : Geometry) (fit : (Layout.oldState c).eval g ≤ 2^g.w)
    (a : Fin (c.labels.eval g)) :
    counterAddr (words c g) a ≠ Fin.ofNat _ (Layout.stageTag.eval g) := by
  have ht := (ranges c g).2.2
  change (Layout.counter c).eval g + c.labels.eval g ≤ 2^g.w at fit
  have ha := a.isLt
  have hc : (Layout.counter c).eval g < 2^g.w := by omega
  have hv : (words c g 2).val = (Layout.counter c).eval g := Nat.mod_eq_of_lt hc
  have hfit : (words c g 2).val + c.labels.eval g ≤ 2^g.w := hv ▸ fit
  intro eq
  have h := congrArg Fin.val eq
  rw [counterAddr_val _ _ hfit, hv, Fin.val_ofNat, Nat.mod_eq_of_lt (ht.trans hc)] at h
  omega

end LiveProgram.ExponentStage

end VPVNP
end Computability
end OAI
