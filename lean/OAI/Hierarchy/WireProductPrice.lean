import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal

namespace OAI
/-! # Exact price of a product of finite equality wires at any placement -/

namespace Hierarchy.WirePrice

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators NNReal

variable {I : Type} [Fintype I] [Nonempty I] {F X : Type*} [Field F] [MetricSpace X]
    (P : SpectralPlacementPrices F X) (x : I → X)

/-- Prices add when a tensor is the product, up to local linear equivalence,
of nonzero factors. The placement can repeat sites. -/
theorem product {E : Type*} [Fintype E] (T : Raw.{0} I F) (U : E → Raw.{0} I F)
    (nonzero : ∀ e, (U e).coeff ≠ 0) (eq : ofRaw T = ∏ e, ofRaw (U e)) :
    P.price T x = ∑ e, P.price (U e) x := by
  rcases P.all_zero_or_normalized_at x with price | ⟨φ,c,_,price⟩
  · simp [price]
  simp only [price,rawLogPrice]
  rw [← Finset.mul_sum]
  congr 1
  change Real.logb 2 (normalizedSpectrum.toRingHom φ (ofRaw T) : ℝ) = _
  rw [eq,map_prod,NNReal.coe_prod]
  apply Real.logb_prod
  intro e _
  apply ne_of_gt
  apply NNReal.coe_pos.mpr
  exact zero_lt_one.trans_le (one_le_raw_spectralValue φ (U e) (nonzero e))

omit [Nonempty I] in
/-- An equality wire of alphabet size q between any two marked labels has
price equal to the distance between its endpoints times the base-two width. -/
theorem wire (q : ℕ) (u v : I) :
    P.price ((Raw.diagonal (Fin 2) F (Fin q)).group ![u,v]) x =
      dist (x u) (x v) * Real.logb 2 q := by
  rw [← P.group]
  exact P.placed_diagonal_pair (x ∘ ![u,v]) q

/-- The exact total charge of a finite collection of wires, allowing all pairs
and any placement of their marked ends. -/
theorem wires {E : Type*} [Fintype E] (u v : E → I) (q : ℕ) (hq : 0 < q)
    (T : Raw.{0} I F)
    (eq : ofRaw T = ∏ e, ofRaw ((Raw.diagonal (Fin 2) F (Fin q)).group ![u e,v e])) :
    P.price T x = ∑ e, dist (x (u e)) (x (v e)) * Real.logb 2 q := by
  let D := Raw.diagonal (Fin 2) F (Fin q)
  have hd : D.coeff ≠ 0 := by
    intro hz
    have h := congrFun hz (fun _ => (⟨0,hq⟩ : Fin q))
    change (Raw.diagonal (Fin 2) F (Fin q)).coeff _ = 0 at h
    simp [Raw.diagonal_coeff_at (0 : Fin 2)] at h
  rw [product P x T (fun e => D.group ![u e,v e]) (fun e => (D.group_ne_zero_iff _).2 hd) eq]
  exact Finset.sum_congr rfl (fun e _ => wire P x q (u e) (v e))

end Hierarchy.WirePrice

end OAI
