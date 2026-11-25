import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformation

/-! # Diagonal transport at the two binomial deformation endpoints

Sending each generator to a scalar multiple of the original generator scales each
basis monomial by one fixed unit, independent of the inputs. This describes the
endpoint changes directly on the arrays used by the circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Matrix
open scoped BigOperators

variable {R σ : Type*} [CommRing R]

private theorem axisCoeff_scale {m : ℕ} (β w : R) (a b k : Fin m) :
    w ^ k.val * axisCoeff (β * w^m) a b k =
      axisCoeff β a b k * (w ^ a.val * w ^ b.val) := by
  by_cases he : k.val = (a.val + b.val) % m
  · by_cases hwrap : a.val+b.val < m
    · simp [axisCoeff, he, hwrap, Nat.mod_eq_of_lt, pow_add]
    · have ha := a.isLt
      have hb := b.isLt
      have hw : (a.val+b.val) % m + m = a.val+b.val := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [axisCoeff, he, ↓reduceIte, ite_eq_right hwrap, ← pow_add]
      calc
        _ = β * w ^ ((a.val+b.val)%m+m) := by rw [pow_add]; ring
        _ = _ := by rw [hw]
  · simp [axisCoeff, he]

variable [Fintype σ]

/-- Change of generator on a power-basis coordinate array. -/
def scale (m : σ → ℕ) (w : σ → Rˣ) (x : Address m → R) (k : Address m) : R :=
  (∏ i, (w i : R) ^ (k i).val) * x k

@[simp] theorem scale_inverse (m : σ → ℕ) (w : σ → Rˣ) (x : Address m → R) :
    scale m w (scale m (fun i => (w i)⁻¹) x) = x := by
  funext k
  simp only [scale, ← mul_assoc, ← Finset.prod_mul_distrib, ← mul_pow, Units.mul_inv, one_pow,
    Finset.prod_const_one, one_mul]

@[simp] theorem inverse_scale (m : σ → ℕ) (w : σ → Rˣ) (x : Address m → R) :
    scale m (fun i => (w i)⁻¹) (scale m w x) = x := by
  simpa only [inv_inv] using scale_inverse m (fun i => (w i)⁻¹) x

variable [DecidableEq σ]

/-- The diagonal generator change intertwines the two wrapped products in coordinates. -/
theorem scale_multiply (m : σ → ℕ) (w : σ → Rˣ) (β β' : σ → R)
    (hw : ∀ i, β i * (w i : R) ^ m i = β' i) (x y : Address m → R) :
    scale m w (multiply (coeff β' m) x y) =
      multiply (coeff β m) (scale m w x) (scale m w y) := by
  have hs (a b k : Address m) :
      (∏ i, (w i : R) ^ (k i).val) * coeff β' m a b k =
        coeff β m a b k * ((∏ i, (w i : R) ^ (a i).val) * ∏ i, (w i : R) ^ (b i).val) := by
    simp only [coeff, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hw i ▸ axisCoeff_scale _ _ (a i) (b i) (k i)
  funext k
  simp only [scale, multiply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (x a * y b) * ((∏ i, (w i : R) ^ (k i).val) * coeff β' m a b k) := by ring
    _ = _ := by rw [hs]; ring

omit [Fintype σ] [DecidableEq σ] in
/-- The lifted roots at zero and at one define unit scalings of the generators. -/
theorem exists_endpoint_scales (r H : ℕ) (m : σ → ℕ) (β : σ → Rˣ)
    (hm : ∀ i, IsUnit (m i : R)) :
    ∃ (v : σ → (Jet R H)ˣ) (u : σ → (Jet R r)ˣ),
      (∀ i, (v i : Jet R H) ^ m i = specialize 0 H (binomial (β i : R))) ∧
      (∀ i, algebraMap R (Jet R r) (β i : R) * (u i : Jet R r) ^ m i =
        specialize 1 r (binomial (β i : R))) := by
  let z (n : ℕ) : Jet R n := AdjoinRoot.root ((X : R[X]) ^ n)
  have hx (a : R) (n : ℕ) : specialize a n X = algebraMap R _ a + z n := by
    change aeval _ (taylor a X) = _
    simp [z, add_comm]
  have he (a : R) (n : ℕ) (i : σ) :
      specialize a n (binomial (β i : R)) =
        1 + (algebraMap R _ (β i : R) - 1) * (algebraMap R _ a + z n) := by
    simp only [binomial, map_add, map_mul, map_one, hx]
    rw [show specialize a n (C ((β i : R)-1)) = _ from (specialize a n).commutes _,
      map_sub, map_one]
  let g (n : ℕ) := algebraMap R (Jet R n)
  choose v _ hv using fun i => binomialScalingAtZero (z H) (g H (β i : R))
    (jetParameter_nilpotent R H) (m i) (by simpa [g] using (hm i).map (g H))
  choose u _ hu using fun i => binomialScalingAtOne (z r) (Units.map (g r) (β i))
    (jetParameter_nilpotent R r) (m i) (by simpa [g] using (hm i).map (g r))
  refine ⟨v, u, fun i => ?_, fun i => ?_⟩
  · simpa only [he, map_zero, zero_add] using hv i
  · rw [he, map_one]
    exact hu i

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
