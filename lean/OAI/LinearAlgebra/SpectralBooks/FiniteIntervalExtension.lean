import OAI.LinearAlgebra.SpectralBooks.SiteTensor.FiniteIntervalPoint
import OAI.LinearAlgebra.SpectralBooks.FinitePriceSpace
import OAI.LinearAlgebra.SpectralBooks.GeodesicExtensionTower

/-! # A metric midpoint extension preserving all finite tensor prices

Normalize the prices on the old sites by their common binary diagonal, adjoin
the interpolating site, and use the same scale when taking the metric quotient.
The quotient preserves every placed price, even when tensor indices coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open SiteTensor

variable {K : Type*} [Field K]

/-- A midpoint in the normalized spectral point gives a metric midpoint
extension of any finite realization of the prices. -/
theorem SpectralPlacementPrices.exists_finite_midpoint_extension : HasFiniteMidpointExtensions K := by
  classical
  intro A a b
  by_cases hab : a = b
  · subst b
    exact ⟨A, PriceEmbedding.refl _, a, by simp [IsWireMidpoint, PriceEmbedding.refl]⟩
  have : Nontrivial A.carrier := ⟨⟨a, b, hab⟩⟩
  let := Fintype.ofFinite A.carrier
  let e := Function.Embedding.refl A.carrier
  let c := A.prices.price (Raw.diagonal A.carrier K (Fin 2)) e
  obtain ⟨φ, hc, normalized⟩ := A.prices.normalized_group e
  obtain ⟨ψ, old, hma, hmb⟩ := exists_midpoint_spectral_point φ a b
  obtain ⟨Y, met, Q, j, hj, hDist, hPrice⟩ := exists_metric_price_realization ψ c hc.le
  let B : FinitePriceSpace K := ⟨Y, met, Finite.of_surjective j hj, Q⟩
  let f := j ∘ some
  have hprice {I : Type} [Fintype I] (T : Raw.{0} I K) (p : I → A.carrier) :
      Q.price T (f ∘ p) = A.prices.price T p := by
    by_cases hT : T.coeff = 0
    · exact (Q.zero_tensor T hT _).trans (A.prices.zero_tensor T hT _).symm
    change Q.price T (j ∘ (some ∘ p)) = _
    rw [hPrice, show A.prices.price T p = _ from normalized p T hT]
    have heq := ofRaw_eq_iff.mpr (Raw.group_group_equivalent T p (some : A.carrier → Option _))
    have hg := old (T.group p)
    simp only [rawLogPrice, one_mul, heq] at hg
    change c * Real.logb 2 (ψ.val _) = c * Real.logb 2 (φ.val _)
    exact congrArg (c * ·) hg
  have hf : Isometry f := by
    apply Isometry.of_dist_eq
    intro x y
    have h := hprice (Raw.diagonal (Fin 2) K (Fin 2)) ![x,y]
    simpa [Q.wire, A.prices.wire] using h
  let emb : PriceEmbedding A.prices B.prices := ⟨f, hf, hprice⟩
  have oldDist : dist a b = c * rawWireDistance φ 1 a b := by
    let W := Raw.diagonal (Fin 2) K (Fin 2)
    have hn : W.coeff ≠ 0 := by
      intro hz
      have h := (A.prices.zero_tensor W hz ![a,b])
      rw [show A.prices.price W ![a,b] = dist a b from A.prices.wire _] at h
      exact hab (dist_eq_zero.mp h)
    have h := normalized ![a, b] W hn
    change A.prices.price W ![a,b] = _ at h
    simpa only [W, A.prices.wire, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, rawWireDistance, rawLogPrice, one_mul] using h
  have halfway (s : A.carrier)
      (hs : rawWireDistance ψ 1 none (some s) = rawWireDistance φ 1 a b / 2) :
      dist (f s) (j none) = dist a b / 2 := by
    change dist (j (some s)) (j none) = _
    rw [dist_comm, hDist, oldDist]
    have hp : rawWireDistance ψ c none (some s) = c * rawWireDistance ψ 1 none (some s) := by
      simp [rawWireDistance, rawLogPrice]
    rw [hp, hs]
    ring
  exact ⟨B, emb, j none, by
    change dist (f a) (j none) = dist (f a) (f b) / 2 ∧
      dist (f b) (j none) = dist (f a) (f b) / 2
    rw [hf.dist_eq]
    exact ⟨halfway _ hma, halfway _ hmb⟩⟩

end

end

end SpectralBooks
end LinearAlgebra
end OAI
