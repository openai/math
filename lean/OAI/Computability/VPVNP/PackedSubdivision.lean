import OAI.Computability.VPVNP.ShrinkEnergy
import OAI.Computability.VPVNP.SlotSubdivision

/-!
# Masses and subdivision counts of an actual packed graph

The color bits and old slot label give exactly `K = 2^c*d` old positions
per packed site. Section 7.2 consequently computes the new arc mass from
the old arc mass and the two degrees alone.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open ShrinkEnergy SlotSubdivision

variable {V H Tag L : Type*} {d c : ℕ}
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]

/-- The number of old positions per packed site is the number of choices
of color word times the number of choices of the old slot label. -/
theorem card_positions (P : PackingData V H Tag L d c) :
    Fintype.card (Position V H Tag L c) = Fintype.card (Site V Tag L) * (2 ^ c * d) := by
  have hH : Fintype.card H = d := (Fintype.card_congr P.slotLabel).trans (Fintype.card_fin _)
  simp only [Position, BitWord, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, hH]

/-- Actual masses satisfy `p' = pKd/d'`. -/
theorem equalArcMass_packed (P : PackingData V H Tag L d c) (hd : 0 < d) (d' : ℕ) :
    equalArcMass (Site V Tag L) d' =
      equalArcMass (Position V H Tag L c) d * ((2 ^ c * d : ℕ) * (d : ℝ)) / d' := by
  let S : ℝ := (2 ^ c * d : ℕ) * (d : ℝ)
  have hS : S ≠ 0 := by dsimp only [S]; positivity
  rw [equalArcMass, equalArcMass, P.card_positions, Nat.cast_mul, mul_assoc]
  change 1 / (_ * (d' : ℝ)) = 1 / (_ * S) * S / d'
  simp only [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (Fintype.card (Site V Tag L) : ℝ)⁻¹ * (S⁻¹ * S) * (d' : ℝ)⁻¹ := by
      rw [inv_mul_cancel₀ hS]
      ring
    _ = _ := by ring

/-- The exact packed role counts and the actual floor choice fit inside
the output degree, so the regularization's common deficit exists. -/
theorem packed_degree_budget {T : Type*} [Fintype T] (q : T → ℝ) (hq : ∀ t, 0 ≤ q t)
    (htotal : ∑ t, q t = 4 / 3) (hc : 2 ≤ c) (hd : 0 < d) (d' : ℕ) :
    d * pieceCount d c * ∑ t, count (2 ^ c * d) d d' (q t) ≤ d' := by
  apply degree_budget q hq htotal (Nat.mul_pos (by positivity) hd) hd
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hc
  have h : 2 ^ (2 + n) * d = 4 * (2 ^ n * d) := by rw [pow_add]; ring
  simp only [pieceCount, h]
  omega

end Compression.PackingData

end VPVNP
end Computability
end OAI
