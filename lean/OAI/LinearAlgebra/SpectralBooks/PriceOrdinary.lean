import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import OAI.LinearAlgebra.SpectralBooks.SiteSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-! # Spectral price of an ordinary sum

For a normalized spectral point on the occupied sites, restriction
monotonicity and direct-sum additivity bound the value of the sum by the
sum of the values. Taking logarithms selects one nonzero summand.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal

/-- Taking the logarithm of a sum bound selects a positive summand. The scale
is allowed to vanish so that this includes a collapsed placement. -/
private theorem exists_logb_summand {L : Type*} [Fintype L] {v : ℝ≥0} (f : L → ℝ≥0)
    (hv : 0 < v) (hs : v ≤ ∑ j, f j) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, 0 < f j ∧ c * Real.logb 2 v ≤ c * Real.logb 2 (f j) + c * Real.logb 2 (Fintype.card L) := by
  classical
  cases isEmpty_or_nonempty L with
  | inl h => simp at hs; exact False.elim (hv.ne' hs)
  | inr h =>
    obtain ⟨j, hj⟩ := Finite.exists_max f
    have hsum : v ≤ (Fintype.card L : ℝ≥0) * f j := calc
      _ ≤ ∑ l, f l := hs
      _ ≤ ∑ _l : L, f j := Finset.sum_le_sum fun l _ => hj l
      _ = _ := by simp
    have hp : 0 < (f j : ℝ) := by exact_mod_cast pos_of_mul_pos_right (hv.trans_le hsum) (by positivity)
    have hn : 0 < (Fintype.card L : ℝ) := by exact_mod_cast (Fintype.card_pos (α := L))
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast hv : 0 < (v : ℝ)) (show (v : ℝ) ≤ (Fintype.card L : ℝ) * f j by exact_mod_cast hsum)
    rw [Real.logb_mul hn.ne' hp.ne'] at hlog
    exact ⟨j, by exact_mod_cast hp, by linarith [mul_le_mul_of_nonneg_left hlog hc]⟩

namespace SiteTensor

/-- The local map at each site adds its two direct-sum blocks. Applying all
these maps to a tensor direct sum gives ordinary addition in the fixed format. -/
theorem ordinary_add_restricts {I K : Type*} [Fintype I] [CommSemiring K]
    {A : I → Type*} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K) :
    Crossing.IsRestriction (T + U) (sumCoeff T U) := by
  classical
  let fold (i : I) (a : A i) (s : A i ⊕ A i) : K := if Sum.elim id id s = a then 1 else 0
  refine ⟨fold, fun x => ?_⟩
  simp only [sumCoeff, add_mul, Finset.sum_add_distrib, Pi.add_apply]
  rw [sum_pushCoeff_mul, sum_pushCoeff_mul]
  have elim (V : (∀ i, A i) → K) :
      (∑ a, V a * ∏ i, (if a i = x i then (1 : K) else 0)) = V x := by
    simp_rw [Fintype.prod_boole]
    simp [← funext_iff, mul_ite]
  exact congrArg₂ (· + ·) (elim T).symm (elim U).symm

universe v
noncomputable section

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable {A : I → Type v} [∀ i, Fintype (A i)]

/-- The restriction class of a coefficient tensor in its given finite format. -/
def ofCoeffs (T : (∀ i, A i) → K) : TensorClass.{v} I K :=
  ofRaw ⟨A, inferInstance, T⟩

@[simp] theorem ofCoeffs_zero : ofCoeffs (0 : (∀ i, A i) → K) = 0 := by
  apply ofRaw_eq_iff.mpr
  constructor <;> exact ⟨fun _ _ _ => 0, fun _ => by simp [Raw.zero]⟩

/-- Local block addition also gives a restriction from a finite direct sum. -/
theorem ordinary_sum_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    ofCoeffs (∑ j, T j) ≤ ∑ j, ofCoeffs (T j) := by
  classical
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (ofRaw_le_iff.mpr (ordinary_add_restricts _ _)).trans (add_mono le_rfl ih)

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- Evaluation by an actual normalized spectral point in fixed tensor spaces. -/
def coeffValue (T : (∀ i, A i) → K) : ℝ≥0 := φ.val (ofCoeffs T)

@[simp] theorem coeffValue_zero : coeffValue φ (0 : (∀ i, A i) → K) = 0 := by
  simp [coeffValue, φ.2.1]

theorem coeffValue_one_le {T : (∀ i, A i) → K} (h : T ≠ 0) : 1 ≤ coeffValue φ T := by
  have hle : (1 : TensorClass.{v} I K) ≤ ofCoeffs T :=
    ofRaw_le_iff.mpr (Crossing.unit_restricts_of_nonzero h)
  simpa [coeffValue, φ.2.2.1] using φ.2.2.2.2.2 _ _ hle

theorem ordinary_sum_value_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K) :
    coeffValue φ (∑ j, T j) ≤ ∑ j, coeffValue φ (T j) := by
  have h := φ.2.2.2.2.2 _ _ (ordinary_sum_le T)
  change coeffValue φ (∑ j, T j) ≤ normalizedSpectrum.toRingHom φ (∑ j, ofCoeffs (T j)) at h
  rw [map_sum] at h
  exact h

/-- Equation `price-ordinary` for a nonnegative multiple of the log of a point
normalized on the occupied site set. Among the nonzero summands, one attains
the stated bound. This also covers zero summands and a collapsed price. -/
theorem ordinary_sum_logb_le {J : Type*} [Fintype J] (T : J → (∀ i, A i) → K)
    (hT : ∑ j, T j ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ j, T j ≠ 0 ∧ c * Real.logb 2 (coeffValue φ (∑ k, T k)) ≤
      c * Real.logb 2 (coeffValue φ (T j)) + c * Real.logb 2 (Fintype.card J) := by
  obtain ⟨j, hj, h⟩ := exists_logb_summand _ (zero_lt_one.trans_le (coeffValue_one_le φ hT))
    (ordinary_sum_value_le φ T) hc
  exact ⟨j, fun h0 => by simp [h0] at hj, h⟩

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
