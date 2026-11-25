import OAI.LinearAlgebra.FiniteFourier.Batched
import OAI.LinearAlgebra.FiniteFourier.BatchedListPrice
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-! # A sparse dictionary after an arbitrary row quotient -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} [Field K] {R C D : Type} [Fintype R] [Fintype C] [Fintype D]

theorem matrixEntryCount_eq_sum (U : Matrix R C K) :
    matrixEntryCount U = ∑ r, (Finset.univ.filter (fun c => U r c ≠ 0)).card := by
  simp only [matrixEntryCount, Finset.card_filter, Fintype.sum_prod_type]

theorem sum_rpow_le_card_mul_mean [Nonempty R] (f : R → ℝ) (hf : ∀ r, 0 ≤ f r)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    ∑ r, f r ^ p ≤ (Fintype.card R : ℝ) * ((∑ r, f r) / Fintype.card R) ^ p := by
  have hR : 0 < (Fintype.card R : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := (Real.concaveOn_rpow hp hp').le_map_sum (t := Finset.univ)
    (w := fun _ : R => (Fintype.card R : ℝ)⁻¹) (p := f)
    (fun _ _ => by positivity) (by simp [hR.ne']) (fun r _ => hf r)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  rw [← div_eq_inv_mul] at h
  rw [mul_comm (Fintype.card R : ℝ)]
  apply (div_le_iff₀ hR).mp
  simpa only [div_eq_inv_mul] using h

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

theorem listValue_sum_le {ι : Type*} (s : Finset ι) (f : ι → Matrix R C K) :
    (listValue φ (∑ i ∈ s, f i) : ℝ) ≤ ∑ i ∈ s, (listValue φ (f i) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp [listValue_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (NNReal.coe_le_coe.mpr (listValue_add_le φ _ _)).trans (add_le_add le_rfl ih)

theorem listValue_dictionary_le [Nonempty R] (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {x a b : Plane} {δ : ℝ} (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (hlen : dist a b ≤ δ) (Q : Matrix D R K) (U : Matrix R C K) :
    (listValue φ (Q * U) : ℝ) ≤ (Fintype.card R : ℝ) *
      ((matrixEntryCount U : ℝ) / Fintype.card R) ^ (dist a b / δ) := by
  let A (r : R) : Matrix D (Fin 1) K := fun i _ => Q i r
  let V (r : R) : Matrix (Fin 1) C K := fun _ j => U r j
  let s (r : R) := Finset.univ.filter (fun c => U r c ≠ 0)
  have hsum : Q * U = ∑ r, A r * V r := by
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    rw [Matrix.mul_apply, Fintype.sum_unique]
  have hs (r : R) : ∀ i c, c ∉ s r → V r i c = 0 := by
    simp [s, V]
  rw [hsum]
  refine (listValue_sum_le φ _ _).trans ((Finset.sum_le_sum fun r _ =>
    listValue_single_le P hflat φ hp hd (A r) (V r) (s r) (hs r)).trans ?_)
  rw [matrixEntryCount_eq_sum, Nat.cast_sum]
  exact sum_rpow_le_card_mul_mean (fun r => ((s r).card : ℝ)) (fun _ => by positivity)
    (by positivity) ((div_le_one hd).mpr hlen)

end FiniteFourier
end LinearAlgebra
end OAI
