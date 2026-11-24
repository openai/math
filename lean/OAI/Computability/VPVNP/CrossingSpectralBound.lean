import OAI.Computability.VPVNP.CrossingPlacement
import OAI.Computability.VPVNP.WireSpectrum

/-!
# Spectral bounds for the two shifted crossing cuts

Section 3.2 of *VP and VNP differ over every field* places four terminals and
two pairs of auxiliary centers at a single spectral point. The two cuts have
independent ranks. This file derives the numerical inequality in the wire
distances from the integral factors and local restrictions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open VPVNP.WireTensor
open scoped NNReal

variable {k J : Type*} [Field k] [Fintype J] (F : SpectralPoint k J)
variable {x y plus minus : ℕ}

/-- The sum of the spectral values of the two cut networks bounds the value
of the original wires, including when some of the wire dimensions vanish. -/
theorem crossing_value_le (p : Terminal → J) (cp cm : Bool → J)
    (f : IntegralCrossing x y plus minus) :
    F.value (terminalWires p x y) ≤ F.value (crossingNetwork p cp false x y plus) +
      F.value (crossingNetwork p cm true x y minus) :=
  (F.monotone (crossingNetworks_restricts p cp cm f)).trans_eq (F.value_directSum _ _)

private theorem card_fin_instance (n : ℕ) (inst : Fintype (Fin n)) :
    @Fintype.card (Fin n) inst = n := by
  exact (@Fintype.card_congr _ _ inst (Fin.fintype n) (Equiv.refl _)).trans (Fintype.card_fin n)

/-- The four terminal wires and one rank wire give the cost of either cut.
Reversing the second wire exchanges its assignments to the two centers. -/
theorem crossingNetwork_value (p : Terminal → J) (c : Bool → J) (flipY : Bool) {rank : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < rank) :
    (F.value (crossingNetwork p c flipY x y rank) : ℝ) =
      (x : ℝ) ^ (F.wireDistance (p (.inl false)) (c false) +
        F.wireDistance (p (.inl true)) (c true)) *
      (y : ℝ) ^ (F.wireDistance (p (.inr flipY)) (c false) +
        F.wireDistance (p (.inr (!flipY))) (c true)) *
      (rank : ℝ) ^ F.wireDistance (c false) (c true) := by
  have hx' : 0 < (x : ℝ) := Nat.cast_pos.mpr hx
  have hy' : 0 < (y : ℝ) := Nat.cast_pos.mpr hy
  let dims : Option Terminal → ℕ
    | none => rank
    | some (.inl _) => x
    | some (.inr _) => y
  have hcard (e : Option Terminal) :
      Fintype.card (cutBasis (terminalBasis x y) (Fin rank) e) = dims e := by
    rcases e with _ | (b | b) <;> exact card_fin_instance _ _
  unfold crossingNetwork
  rw [F.value_wireNetwork_eq_prod_rpow]
  · simp only [hcard, Fintype.prod_option, Fintype.prod_sum_type, Fintype.prod_bool]
    cases flipY <;>
      simp only [dims, cutSource, cutTarget, cutSide, Bool.xor_false, Bool.xor_true,
        Bool.not_true, Bool.not_false, Real.rpow_add hx', Real.rpow_add hy'] <;> ring
  · intro e
    rw [hcard]
    rcases e with _ | (b | b)
    · exact hr
    · exact hx
    · exact hy

/-- The spectral inequality used in the proof of norm rigidity. Both pairs
of centers and all four terminals may occupy arbitrary, even coincident,
parties at the same spectral point. The cut ranks need not agree. -/
theorem crossing_spectral_inequality (p : Terminal → J) (cp cm : Bool → J)
    (hx : 0 < x) (hy : 0 < y) (hp : 0 < plus) (hm : 0 < minus)
    (f : IntegralCrossing x y plus minus) :
    (x : ℝ) ^ F.wireDistance (p (.inl false)) (p (.inl true)) *
      (y : ℝ) ^ F.wireDistance (p (.inr false)) (p (.inr true)) ≤
    (x : ℝ) ^ (F.wireDistance (p (.inl false)) (cp false) +
      F.wireDistance (p (.inl true)) (cp true)) *
    (y : ℝ) ^ (F.wireDistance (p (.inr false)) (cp false) +
      F.wireDistance (p (.inr true)) (cp true)) *
    (plus : ℝ) ^ F.wireDistance (cp false) (cp true) +
    (x : ℝ) ^ (F.wireDistance (p (.inl false)) (cm false) +
      F.wireDistance (p (.inl true)) (cm true)) *
    (y : ℝ) ^ (F.wireDistance (p (.inr true)) (cm false) +
      F.wireDistance (p (.inr false)) (cm true)) *
    (minus : ℝ) ^ F.wireDistance (cm false) (cm true) := by
  have h := NNReal.coe_le_coe.mpr (crossing_value_le F p cp cm f)
  simpa only [terminalWires, F.value_tensorProduct, NNReal.coe_mul, NNReal.coe_add,
    F.value_wire_eq_rpow _ _ hx, F.value_wire_eq_rpow _ _ hy,
    crossingNetwork_value F p cp false hx hy hp, crossingNetwork_value F p cm true hx hy hm,
    Bool.not_true, Bool.not_false] using h

end Crossing

end VPVNP
end Computability
end OAI
