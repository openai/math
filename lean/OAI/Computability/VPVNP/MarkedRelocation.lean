import OAI.Computability.VPVNP.MarkedExteriorBound
import OAI.Computability.VPVNP.MarkedPowers
import OAI.Computability.VPVNP.MarkedMove
import OAI.Computability.VPVNP.WireGeodesic

/-!
# Relocation of one marked tensor index

In Lemma A.1 of *VP and VNP differ over every field*, exterior multiplication
and contraction on the marked index split its product with a wire. Dividing
by the wire value leaves two ratios of adjacent exterior dimensions. Their
bounds over tensor powers yield geometric interpolation of the endpoint
values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor.SpectralPoint

open WireGeometry
open scoped NNReal

universe u v

variable {k : Type u} {J : Type v} [Field k] [Fintype J]

private theorem divide_exterior_wire {x y z h p m u t : ℝ} (hh : 0 < h)
    (hp : 0 ≤ p) (hm : 0 ≤ m)
    (bound : x * h ^ t ≤ y * h ^ (u * t) * p ^ ((1 - u) * t) +
      z * m ^ (u * t) * h ^ ((1 - u) * t)) :
    x ≤ y * (p / h) ^ ((1 - u) * t) + z * (m / h) ^ (u * t) := by
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hh t)).mp
  calc
    x * h ^ t ≤ _ := bound
    _ = (y * (p / h) ^ ((1 - u) * t) + z * (m / h) ^ (u * t)) * h ^ t := by
      rw [show h ^ t = h ^ (u * t) * h ^ ((1 - u) * t) by rw [← Real.rpow_add hh]; congr 1; ring]
      rw [Real.div_rpow hp hh.le, Real.div_rpow hm hh.le]
      field_simp

private theorem geometric_bound_of_equal_values {x y z u : ℝ} (hx : 0 < x)
    (hy : x = y) (hz : x = z) : x ≤ y ^ (1 - u) * z ^ u := by
  rw [← hy, ← hz, ← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]

/-- Lemma A.1. Placing a marked tensor index at a fractional point gives a
spectral value bounded by the weighted geometric mean of the endpoint
placements. The bound also holds for zero coefficient arrays. -/
theorem value_marked_atFraction_le (F : SpectralPoint k J) (B : J → Type)
    [∀ j, Fintype (B j)] (I : Type) [Fintype I] (a b c : J)
    (T : ((j : J) → B j) → I → k) {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1)
    (hfrac : @AtFraction J F.wirePseudoMetric a b u c) :
    (F.value (marked B I c T) : ℝ) ≤
      (F.value (marked B I a T) : ℝ) ^ (1 - u) * (F.value (marked B I b T) : ℝ) ^ u := by
  classical
  let v (j : J) : ℝ := F.value (marked B I j T)
  change v c ≤ v a ^ (1 - u) * v b ^ u
  have hnonneg (j : J) : 0 ≤ v j := (F.value _).coe_nonneg
  by_cases hz : F.value (marked B I c T) = 0
  · have hc : v c = 0 := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hz
    rw [hc]
    exact mul_nonneg (Real.rpow_nonneg (hnonneg a) _) (Real.rpow_nonneg (hnonneg b) _)
  have hpos (j : J) : 0 < v j := by
    apply lt_of_le_of_ne (hnonneg j)
    intro h
    exact hz ((F.value_marked_eq_zero_iff B I j c T).mp (NNReal.eq h.symm))
  have hI : Nonempty I := by
    rcases isEmpty_or_nonempty I with h | h
    · exact False.elim <| hz <| F.value_zero _ (funext fun x ↦ isEmptyElim ((x c).2 rfl))
    · exact h
  have hIpos := Fintype.card_pos (α := I)
  obtain ⟨hac, hcb⟩ := hfrac
  change F.wireDistance a c = u * F.wireDistance a b at hac
  change F.wireDistance c b = (1 - u) * F.wireDistance a b at hcb
  by_cases ht : F.wireDistance a b = 0
  · rw [ht, mul_zero] at hac hcb
    exact geometric_bound_of_equal_values (hpos c)
      (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (F.value_marked_eq_of_dist_zero B I a c T hac).symm)
      (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (F.value_marked_eq_of_dist_zero B I c b T hcb))
  by_cases hOne : Fintype.card I = 1
  · exact geometric_bound_of_equal_values (hpos c)
      (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (F.value_marked_eq_of_card_one B I c a T hOne))
      (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (F.value_marked_eq_of_card_one B I c b T hOne))
  have ht' : 0 < F.wireDistance a b := lt_of_le_of_ne (F.wireDistance_nonneg _ _) (Ne.symm ht)
  have hq : 2 ≤ Fintype.card I := by omega
  obtain ⟨hs₀, hs₁⟩ := relocation_log_bounds hq (hpos b) (hpos a) ht'
    (F.value_marked_move_le B I a b T) (by
      rw [F.wireDistance_comm a b]
      exact F.value_marked_move_le B I b a T)
  apply relocation_of_power_bounds hq (hpos b) (hpos a) ht' hu₀ hu₁ hs₀ hs₁
  intro n _ h hh hQ
  let Bn (j : J) := Fin n → B j
  let Q := Fintype.card I ^ n
  let Tn (x : (j : J) → Bn j) (i : Fin Q) := markedPowerTable n T x ((markedPowerIndex I n).symm i)
  have hv (j : J) : (F.value (marked Bn (Fin Q) j Tn) : ℝ) = v j ^ n := by
    simpa only [Bn, Q, Tn, v, NNReal.coe_pow] using
      congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) (F.value_markedPower_fin B I j T n)
  have bound := F.value_marked_exterior_bound Bn hh hQ c a b Tn
  rw [hv, hv, hv, hac, hcb] at bound
  obtain ⟨hposH, _, _⟩ := VPVNP.ExteriorLevelRates.choose_adjacent_pos hh hQ
  exact divide_exterior_wire (by exact_mod_cast hposH) (by positivity) (by positivity) bound

end WireTensor.SpectralPoint

end VPVNP
end Computability
end OAI
