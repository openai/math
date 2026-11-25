import OAI.LinearAlgebra.SpectralBooks.PlacementPullback
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Placement prices used in the two-cut comparison -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
namespace SpectralPlacementPrices

open SiteTensor

variable {I : Type} [Fintype I] [Nonempty I] {E K : Type*} [MetricSpace E] [Field K]
    (P : SpectralPlacementPrices K E)

/-- A single price normalization applies to all formats at a fixed placement.
The constant placement has price zero on all tensors. -/
theorem all_zero_or_normalized_at (p : I → E) :
    (∀ T : Raw.{0} I K, P.price T p = 0) ∨
      ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ),
        0 < c ∧ ∀ T : Raw.{0} I K, P.price T p = rawLogPrice φ c T := by
  obtain ⟨g, hg, hp⟩ := P.exists_spectralPrice_of_placement p
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · exact Or.inl fun T => (hp T).trans (classPrice_zero _)
  · exact Or.inr ⟨φ, c, hc, fun T => (hp T).trans (classPrice_scaled_log φ c _)⟩

theorem placed_mono (p : I → E) {X Y : Raw.{0} I K} (h : X.Restricts Y) :
    P.price X p ≤ P.price Y p := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, hc, hp⟩
  · simp [hz]
  · simpa only [hp] using rawLogPrice_mono φ hc.le h

theorem placed_product (p : I → E) {X Y : Raw.{0} I K} (hx : X.coeff ≠ 0) (hy : Y.coeff ≠ 0) :
    P.price (X.mul Y) p = P.price X p + P.price Y p := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, _, hp⟩
  · simp [hz]
  · simp only [hp, rawLogPrice_mul φ c X Y hx hy]

/-- A fixed placement costs at most one constant extra for a sum of two tensors,
independently of all leg dimensions. -/
theorem exists_binary_sum_overhead (p : I → E) : ∃ C : ℝ,
    ∀ {A : I → Type} [∀ i, Fintype (A i)] (T U : (∀ i, A i) → K), T + U ≠ 0 →
      P.price ⟨A, inferInstance, T + U⟩ p ≤
        max (P.price ⟨A, inferInstance, T⟩ p) (P.price ⟨A, inferInstance, U⟩ p) + C := by
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, hc, hp⟩
  · exact ⟨0, fun _ _ _ => by simp [hz]⟩
  refine ⟨c, ?_⟩
  intro A _ T U h
  let H : Fin 2 → (∀ i, A i) → K := ![T,U]
  have hs : ∑ i, H i = T + U := by simp [Fin.sum_univ_two, H]
  obtain ⟨j, _, hj⟩ := ordinary_sum_logb_le φ H (hs ▸ h) hc.le
  rw [hs] at hj
  simp only [hp]
  fin_cases j <;> simp [H] at hj
  · exact hj.trans (add_le_add_left (le_max_left _ _) _)
  · exact hj.trans (add_le_add_left (le_max_right _ _) _)

/-- A two-terminal identity wire of dimension q. -/
theorem placed_diagonal_pair (p : Fin 2 → E) (q : ℕ) :
    P.price (Raw.diagonal (Fin 2) K (Fin q)) p = dist (p 0) (p 1) * Real.logb 2 q := by
  rw [← P.wire p]
  rcases P.all_zero_or_normalized_at p with hz | ⟨φ, c, _, hp⟩
  · simp [hz]
  simp only [hp, rawLogPrice, ofRaw_diagonal_fin_eq_natCast, Nat.cast_ofNat]
  have he (n : ℕ) : φ.val (n : TensorClass.{0} (Fin 2) K) = n :=
    map_natCast (normalizedSpectrum.toRingHom φ) n
  rw [he q, show (2 : TensorClass.{0} (Fin 2) K) = ((2 : ℕ) : TensorClass.{0} (Fin 2) K) from rfl,
      he 2]
  norm_num [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]

end SpectralPlacementPrices

end

end SpectralBooks
end LinearAlgebra
end OAI
