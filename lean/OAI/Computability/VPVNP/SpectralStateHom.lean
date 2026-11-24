import OAI.Computability.VPVNP.SpectralLocalization
import OAI.Computability.VPVNP.SpectralSeparation
import OAI.Computability.VPVNP.SpectralStates

/-!
# Multiplicativity of extreme states on tensor fractions

In Appendix A.1 the reciprocal of `1 + s` splits the normalized unit into
two positive summands. Extremality makes each summand act multiplicatively.
Restricting the resulting state to the original semiring gives a spectral point.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- A unit whose multiplication preserves an order-unit cone has strictly
positive value at every normalized positive state. -/
theorem state_pos_of_unit_multiplier {P : PointedCone ℚ A} {f : A → ℝ}
    (hf : f ∈ states P) (orderUnit : ∀ x : A, ∃ n : ℕ, n • (1 : A) + x ∈ P)
    {v : A} (hv : IsUnit v) (hstable : ∀ x ∈ P, v * x ∈ P) : 0 < f v := by
  obtain ⟨w, hw⟩ := hv.exists_right_inv
  obtain ⟨n, hn⟩ := orderUnit (-w)
  have hp := hstable _ hn
  simp only [mul_add, mul_smul_comm, mul_one, mul_neg, hw] at hp
  let L := stateLinearMap hf
  have h1 : L 1 = 1 := hf.1
  have hval : 0 ≤ L (n • v + -(1 : A)) := hf.2.2.2 _ hp
  simp only [map_add, map_neg, map_nsmul, h1] at hval
  rw [nsmul_eq_mul] at hval
  change 0 < L v
  by_contra! h
  have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n) h
  linarith

/-- A tensor unit acts multiplicatively on every extreme state when it and
the reciprocal of its sum with the unit preserve the cone. -/
theorem extreme_state_mul_of_unit_denominator {P : PointedCone ℚ A} {f : A → ℝ}
    (he : f ∈ (states P).extremePoints ℝ)
    (orderUnit : ∀ x : A, ∃ n : ℕ, n • (1 : A) + x ∈ P)
    {s v : A} (hs : IsUnit s) (hden : v * (1 + s) = 1)
    (ss : ∀ x ∈ P, s * x ∈ P) (sv : ∀ x ∈ P, v * x ∈ P) (x : A) :
    f (s * x) = f s * f x := by
  have hv : IsUnit v := .of_mul_eq_one _ hden
  have su (y : A) (hy : y ∈ P) : (v * s) * y ∈ P := by
    rw [mul_assoc]
    exact sv _ (ss _ hy)
  apply extreme_state_mul_generator he (u := v * s) (v := v) _ rfl
    (state_pos_of_unit_multiplier he.1 orderUnit (hv.mul hs) su)
    (state_pos_of_unit_multiplier he.1 orderUnit hv sv) su sv x
  simpa only [mul_add, mul_one, add_comm v] using hden

section Tensor

variable {S : Type*} [CommSemiring S] [NoZeroDivisors S] [Nontrivial S] [Preorder S] [CharZero S]
variable {H : OrderBounds S} {f : Spectral.A S → ℝ}

/-- Extreme states multiply by every tensor in the localization. -/
theorem extreme_state_mul_tensor
    (he : f ∈ (states (orderCone toA H)).extremePoints ℝ) (rank : S →+* ℕ)
    (s : S) (x : Spectral.A S) : f (toA s * x) = f (toA s) * f x := by
  by_cases hs : s = 0
  · subst s
    have hzero : f 0 = 0 := map_zero (stateLinearMap he.1)
    simp only [map_zero, zero_mul, hzero]
  · let hn := one_add_ne_zero_of_rank rank s
    let v := fractionInverse (1 + s) hn
    have hden : v * (1 + toA s) = 1 := by
      simpa only [v, map_add, map_one] using fraction_inverse_spec (1 + s) hn
    exact extreme_state_mul_of_unit_denominator he (orderCone_bound H) (toA_isUnit hs) hden
      (fun _ => orderCone_mul_tensor H s) (fun _ => orderCone_mul_inv H _ hn) x

/-- Restriction of an extreme state to the original tensor semiring. -/
noncomputable def extremeStateHom (he : f ∈ (states (orderCone toA H)).extremePoints ℝ)
    (rank : S →+* ℕ) : S →+* ℝ where
  toFun s := f (toA s)
  map_zero' := by rw [map_zero]; exact map_zero (stateLinearMap he.1)
  map_one' := by rw [map_one]; exact he.1.1
  map_add' a b := by rw [map_add]; exact he.1.2.1 _ _
  map_mul' a b := by rw [map_mul]; exact extreme_state_mul_tensor he rank _ _

@[simp] theorem extremeStateHom_apply (he : f ∈ (states (orderCone toA H)).extremePoints ℝ)
    (rank : S →+* ℕ) (s : S) : extremeStateHom he rank s = f (toA s) := rfl

theorem monotone_extremeStateHom (he : f ∈ (states (orderCone toA H)).extremePoints ℝ)
    (rank : S →+* ℕ) : Monotone (extremeStateHom he rank) := by
  intro a b hab
  let L := stateLinearMap he.1
  have hp : toA b - toA a ∈ orderCone toA H := fractionPositive_difference hab
  have h : 0 ≤ L (toA b - toA a) := he.1.2.2.2 _ hp
  exact sub_nonneg.mp (by rwa [map_sub] at h)

/-- Strict comparison at every spectral point places the corresponding
difference inside the order cone of the localization. -/
theorem fractionPositive_of_spectrum_lt (H : OrderBounds S)
    (rank : S →+* ℕ) (hmono : Monotone rank) (x y : S)
    (hlt : ∀ F : S →+* ℝ, Monotone F → F x < F y) :
    FractionPositive toA (toA y - toA x) := by
  let P := orderCone toA H
  let z := toA y - toA x
  change z ∈ P
  by_contra hz
  obtain ⟨L, hL1, hLp, hLz⟩ := separate_order_unit P 1 z (one_mem_orderCone H)
    (neg_one_notMem_orderCone H rank hmono) (orderCone_bound H) hz
  have hL : (⇑L : Spectral.A S → ℝ) ∈ states P :=
    ⟨hL1, L.map_add, L.map_smul, hLp⟩
  obtain ⟨f, he, hfle⟩ := exists_extreme_state_le P (orderCone_bound H) z hL
  have hneg : f z ≤ 0 := hfle.trans hLz
  have hpos := hlt (extremeStateHom he rank) (monotone_extremeStateHom he rank)
  let g := stateLinearMap he.1
  have hpos' : 0 < g (toA y) - g (toA x) := sub_pos.mpr hpos
  rw [← map_sub] at hpos'
  exact hpos'.not_ge hneg

end Tensor

end Spectral

end VPVNP
end Computability
end OAI
