import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCoordinates
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumQueries

/-! # Every ordinary query power is the common kernel in label coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {ℓ : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
variable {C J U E : Type*} [Fintype C] [Fintype J] [Fintype U]
variable [AddCommGroup E] [Module (ZMod ℓ) E]

/-- Simultaneous spectral exponent of each query, in the ordinary array's frequencies. -/
def primeCommonQueryExponents (ω : PrimeSpectrumDigits (C × (J ⊕ U)) ℓ) (j : J) : ZMod ℓ :=
  primeQueryExponent (Function.curry ω.1) (Function.curry ω.2) j

private theorem toMatrixEntry_instances {I : Type*} (d d' : DecidableEq I) (f f' : Fintype I)
    (L : (I → K) →ₗ[K] (I → K)) (o i : I) :
    (@LinearMap.toMatrix' K _ I I d f L) o i = (@LinearMap.toMatrix' K _ I I d' f' L) o i := by
  cases Subsingleton.elim d d'
  cases Subsingleton.elim f f'
  rfl

/-- The common-coordinate transfer on a diagonal label block is exactly the
matrix of the specified power of the ordinary query. This identity holds
simultaneously for all choices of distinguished slot and paired label charts. -/
theorem primeCommonKernel_eq_queryPower (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (B : E →ₗ[ZMod ℓ] E →ₗ[ZMod ℓ] ZMod ℓ)
    (p q : (Unit ⊕ U → ZMod ℓ) ≃ₗ[ZMod ℓ] E)
    (hpq : ∀ x y, B (p x) (q y) = dotProduct x y)
    (j : J) (a : (ZMod ℓ)ˣ) :
    (primeCommonKernel (C := C) (T := PrimeCommonSpectators C j ℓ) hζ B a (Fintype.card (Unit ⊕ U))).submatrix
      (primeCommonQueryChart j p q) (primeCommonQueryChart j p q) =
      ((primeSpectrumQuery hζ (fun ω => primeCommonQueryExponents ω j)) ^ (a : ZMod ℓ).val).toMatrix' := by
  let A := (dotProductBilin (ZMod ℓ) (ZMod ℓ) :
    (Unit ⊕ U → ZMod ℓ) →ₗ[ZMod ℓ] (Unit ⊕ U → ZMod ℓ) →ₗ[ZMod ℓ] ZMod ℓ)
  have hc := primeCommonKernel_chart (C := C) (T := PrimeCommonSpectators C j ℓ)
    hζ a (Fintype.card (Unit ⊕ U)) A B p q hpq
  change ((primeCommonKernel (C := C) (T := PrimeCommonSpectators C j ℓ) hζ B a
    (Fintype.card (Unit ⊕ U))).submatrix (primeCommonChart p q) (primeCommonChart p q)).submatrix (primeCommonQueryPack j)
    (primeCommonQueryPack j) = _
  rw [hc]
  ext o i
  have hp := primeSpectrumQuery_pow_matrix (ι := C × (J ⊕ U)) hζ
    (fun ω => primeCommonQueryExponents ω j) (a : ZMod ℓ) o i
  refine Eq.trans ?_ (hp.symm.trans (toMatrixEntry_instances _ _ _ _ _ o i))
  have hk := primeCommonSplit_kernel hζ j a i.1 i.2 o.1 o.2
  refine Eq.trans ?_ hk.symm |>.trans ?_
  · have hs : (primeCommonQueryPack j i).2 = (primeCommonQueryPack j o).2 ↔
        i.1 ∘ primeQuerySpectatorSlot j = o.1 ∘ primeQuerySpectatorSlot j ∧
        i.2 ∘ primeQuerySpectatorSlot j = o.2 ∘ primeQuerySpectatorSlot j :=
      Prod.mk.injEq .. |>.to_iff
    simp only [Matrix.submatrix_apply, primeCommonKernel]
    by_cases h : (primeCommonQueryPack j i).2 = (primeCommonQueryPack j o).2
    · rw [ite_eq_left h, ite_eq_left (hs.mp h), mul_one, Fintype.card_prod]
      congr 2
      change (↑a⁻¹ : ZMod ℓ) * ∑ c, ∑ u, (i.1 (primeQueryActiveSlot j (c,u)) -
        o.1 (primeQueryActiveSlot j (c,u))) * (o.2 (primeQueryActiveSlot j (c,u)) -
          i.2 (primeQueryActiveSlot j (c,u))) = _
      simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, mul_left_comm (↑a⁻¹ : ZMod ℓ)]
    · rw [ite_eq_right h, ite_eq_right (hs.not.mp h), mul_zero]
  · congr 1
    exact Finset.sum_congr (by ext; simp) fun X _ => Finset.sum_congr (by ext; simp) fun Z _ => rfl

end

end

end FiniteFourier
end LinearAlgebra
end OAI
