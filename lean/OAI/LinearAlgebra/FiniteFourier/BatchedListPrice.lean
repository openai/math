import OAI.LinearAlgebra.FiniteFourier.BatchedProjectedList
import OAI.LinearAlgebra.FiniteFourier.MatrixWire
import OAI.LinearAlgebra.FiniteFourier.TriangleLabelPrice

/-! # Transport of the vector leg of a list -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical NNReal

variable {K : Type*} [Field K] {R C D : Type} [Fintype R] [Fintype C] [Fintype D]
variable (P : SpectralPlacementPrices K Plane)
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)

include hflat in
theorem listPrice_factor_le (A : Matrix R D K) (U : Matrix D C K)
    (s : Finset C) (hs : ∀ r c, c ∉ s → U r c = 0) (x a b hub : Plane) :
    P.price (listRaw (A * U)) ![x,a,b] ≤
      (dist hub a + dist hub b + dist a b) / 2 * Real.logb 2 s.card +
      dist x hub * Real.logb 2 (Fintype.card D) := by
  have ht := P.transport (listRaw U) ![x,a,b] ![hub,a,b]
  rw [Real.dist_eq, Fin.sum_univ_three] at ht
  change |P.price (listRaw U) ![x,a,b] - P.price (listRaw U) ![hub,a,b]| ≤
    dist x hub * Real.logb 2 (Fintype.card D) + dist a a * Real.logb 2 (Fintype.card C) +
    dist b b * Real.logb 2 (Fintype.card C) at ht
  simp only [dist_self, zero_mul, add_zero] at ht
  have hl := placed_price_mono P ![hub,a,b] (listRaw_restricts_supported U s hs)
  rw [triangle_label_price P hflat, Fintype.card_coe] at hl
  apply (placed_price_mono P ![x,a,b] (listRaw_mul_restricts A U)).trans
  linarith [le_abs_self (P.price (listRaw U) ![x,a,b] - P.price (listRaw U) ![hub,a,b])]

include hflat in
theorem listPrice_rank_le (W : Matrix R C K) (x a b hub : Plane) :
    P.price (listRaw W) ![x,a,b] ≤
      (dist hub a + dist hub b + dist a b) / 2 * Real.logb 2 (Fintype.card C) +
      dist x hub * Real.logb 2 W.rank := by
  obtain ⟨A, U, _, _, hfac, _⟩ := matrix_wire_factors W
  have ht := listPrice_factor_le P hflat A U Finset.univ (by simp) x a b hub
  simpa only [← hfac, Finset.card_univ, Fintype.card_fin] using ht

include hflat in
theorem listPrice_single_le (A : Matrix R (Fin 1) K) (U : Matrix (Fin 1) C K)
    (s : Finset C) (hs : ∀ r c, c ∉ s → U r c = 0) (x a b : Plane) :
    P.price (listRaw (A * U)) ![x,a,b] ≤ dist a b * Real.logb 2 s.card := by
  have ht := listPrice_factor_le P hflat A U s hs x a b a
  simpa only [dist_self, zero_add, add_self_div_two, Fintype.card_fin, Nat.cast_one,
    Real.logb_one, mul_zero, add_zero] using ht

variable {x a b : Plane} {δ : ℝ}
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

def PricesListsAt (x a b : Plane) (δ : ℝ) : Prop :=
  ∀ (R C : Type) [Fintype R] [Fintype C] (U : Matrix R C K),
    P.price (listRaw U) ![x,a,b] = δ * Real.logb 2 (listValue φ U : ℝ)

include hflat in
theorem exists_list_triangle_point (x a b : Plane) (hab : 0 < dist a b) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop),
      PricesListsAt P ψ x a b ((dist x a + dist x b + dist a b) / 2) := by
  let diag := Raw.diagonal (Fin 3) K (Fin 2)
  have hd : P.price diag ![x,a,b] = (dist x a + dist x b + dist a b) / 2 := by
    simp [diag, triangle_label_price P hflat]
  rcases placed_price_normalized_or_collapsed P ![x,a,b] with hc | ⟨ψ, c, _, he⟩
  · linarith [hc diag, dist_nonneg (x := x) (y := a), dist_nonneg (x := x) (y := b)]
  have hc : P.price diag ![x,a,b] = c := by
    rw [he, rawLogPrice]
    unfold diag
    rw [ofRaw_diagonal_eq_natCast, show ψ.val (Fintype.card (Fin 2) : TensorClass (Fin 3) K) =
      Fintype.card (Fin 2) from map_natCast (normalizedSpectrum.toRingHom ψ) _]
    simp
  refine ⟨ψ, ?_⟩
  intro R C _ _ U
  rw [← hd, hc, he]
  rfl

theorem listValue_zero : listValue φ (0 : Matrix R C K) = 0 := by
  have hz : (listRaw (0 : Matrix R C K)).coeff = 0 := by
    funext z
    change (if (z 1 : C) = z 2 then (0 : K) else 0) = 0
    exact ite_self _
  exact (congrArg φ.val ((ofRaw_eq_zero_iff _).mpr hz)).trans φ.2.1

theorem listValue_le_of_price_le (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (U : Matrix R C K) {t : ℝ} (ht : 0 < t)
    (h : P.price (listRaw U) ![x,a,b] ≤ δ * Real.logb 2 t) :
    (listValue φ U : ℝ) ≤ t := by
  rcases (listValue φ U).coe_nonneg.eq_or_lt with hz | hu
  · exact hz.symm.trans_le ht.le
  rw [hp R C U] at h
  by_contra! hlt
  exact (not_lt_of_ge (le_of_mul_le_mul_left h hd))
    ((Real.logb_lt_logb_iff (by norm_num : (1:ℝ) < 2) ht hu).mpr hlt)

include hflat in
theorem listValue_single_le (hp : PricesListsAt P φ x a b δ) (hd : 0 < δ)
    (A : Matrix R (Fin 1) K) (U : Matrix (Fin 1) C K)
    (s : Finset C) (hs : ∀ r c, c ∉ s → U r c = 0) :
    (listValue φ (A * U) : ℝ) ≤ (s.card : ℝ) ^ (dist a b / δ) := by
  by_cases hempty : s = ∅
  · have hU : U = 0 := Matrix.ext (fun r c => hs r c (by simp [hempty]))
    rw [hU, Matrix.mul_zero, listValue_zero, NNReal.coe_zero]
    positivity
  have hpos : 0 < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  apply listValue_le_of_price_le P φ hp hd _ (by positivity)
  apply (listPrice_single_le P hflat A U s hs x a b).trans
  rw [Real.logb_rpow_eq_mul_logb_of_pos hpos]
  exact le_of_eq (by field_simp)

end FiniteFourier
end LinearAlgebra
end OAI
