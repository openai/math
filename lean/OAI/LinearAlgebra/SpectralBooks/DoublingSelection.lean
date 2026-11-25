import OAI.LinearAlgebra.SpectralBooks.PrivateProducts
import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum

/-! # Price selection on the tensor semiring of an actual field

All tensors, including those occupying auxiliary sites, are priced on the same
restriction quotient. The only ordinary-sum estimate used in the selection is
for a positive binary diagonal power times one tensor private to each side.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor.BookFactors

open PermutationStretch
open scoped NNReal

variable {K : Type*} [Field K] {B C O : Type} [Fintype B] [Fintype C] [Fintype O]

/-- The binary diagonal on a private side, retaining a basis at the common site. -/
def privateDiagonal (K : Type*) [Field K] (B : Type) : PrivateData K B where
  Center := Fin 2
  Leg _ := Fin 2
  finiteCenter := inferInstance
  finiteLeg _ := inferInstance
  coeff := diagonalCoeff
  coeff_ne h := by
    simpa [diagonalCoeff] using congrFun (congrFun h 0) (fun _ => 0)

/-- The compactness step of doubling, with all semiring and restriction data
instantiated. Its two inputs from tensor comparison are explicitly named.
Private agreement is needed here at the anchor on the first side to fix the
common scale. Agreement at all other private tensors is used in proving the
ordinary-sum estimate `stretch`. -/
theorem doubling_of_class_stretch
    (strict : StrictSpectralComparison.{0} (BookSite B C ⊕ O) K)
    (a b c : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ)
    (ha : IsSpectralPrice unit_le_nonzeroClass a)
    (hb : IsSpectralPrice unit_le_nonzeroClass b)
    (hc : IsSpectralPrice unit_le_nonzeroClass c)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hD : 0 < a ((privateDiagonal K B).left O C))
    (hag : b ((privateDiagonal K B).left O C) = a ((privateDiagonal K B).left O C))
    (stretch : ∀ {k L : ℕ}, 0 < k →
      ∀ (p : PrivateData K B) (q : PrivateData K C)
        (Z : Fin L → NonzeroProduct.{0} (BookSite B C ⊕ O) K),
      let x := k • jointDiagonal K B C O + p.left O C + q.right O B
      ClassOrdinarySum x L Z → ∃ l,
        (lam • a + b + c) x ≤ (lam • a + b + c) (Z l) +
          ((lam + 1) * a ((privateDiagonal K B).left O C) +
            a ((privateDiagonal K C).right O B)) * Real.logb 2 L) :
    ∃ g : NonzeroProduct.{0} (BookSite B C ⊕ O) K →+ ℝ,
      IsSpectralPrice unit_le_nonzeroClass g ∧
      (∀ t, g t ≤ (lam • a + b + c) t) ∧
      (∀ p : PrivateData K B, g (p.left O C) = (lam • a + b + c) (p.left O C)) ∧
      (∀ q : PrivateData K C, g (q.right O B) = (lam • a + b + c) (q.right O B)) ∧
      g (jointDiagonal K B C O) = (lam • a + b + c) (jointDiagonal K B C O) := by
  have hne : (normalizedSpectrum
      (S := TensorClass.{0} (BookSite B C ⊕ O) K) (· ≤ ·)).Nonempty := by
    rcases ha with hz | ⟨f, _, _, _⟩
    · simp [hz] at hD
    · exact ⟨f.val, f.property⟩
  have h₂ : (2 : TensorClass.{0} (BookSite B C ⊕ O) K) ∈ nonzeroClasses _ _ := by
    obtain ⟨v, hv⟩ := hne
    let f := normalizedSpectrum.toRingHom ⟨v, hv⟩
    change (2 : TensorClass.{0} (BookSite B C ⊕ O) K) ≠ 0
    intro heq
    have hbad := congrArg f heq
    rw [map_ofNat, map_zero] at hbad
    norm_num at hbad
  have hcost : 0 ≤ (lam + 1) * a ((privateDiagonal K B).left O C) +
      a ((privateDiagonal K C).right O B) :=
    add_nonneg (mul_nonneg (by positivity) hD.le) (ha.nonneg _)
  have hanchor : 0 < (lam • a + b + c) ((privateDiagonal K B).left O C) := by
    change 0 < lam * _ + b _ + c _
    rw [hag]
    linarith only [hD, mul_nonneg hlam hD.le, hc.nonneg ((privateDiagonal K B).left O C)]
  obtain ⟨g, hg, hle, heq⟩ := spectral_price_of_permutation_stretch unit_le_nonzeroClass h₂
    exists_le_natCast hne ClassOrdinarySum (expandedStrictComparison_of_strict strict)
    (targetProducts K B C O) (jointDiagonal K B C O) ((privateDiagonal K B).left O C)
    (left_mem _) a b c ha hb hc lam _ hlam hcost hanchor (by
      intro x hx m L Z hm hZ
      obtain ⟨k, hk, p, q, heq⟩ := power_target hx hm
      rw [heq] at hZ ⊢
      exact stretch hk p q Z hZ)
  exact ⟨g, hg, hle, fun p => heq _ (left_mem p), fun q => heq _ (right_mem q), heq _ diagonal_mem⟩

end SiteTensor.BookFactors

end

end SpectralBooks
end LinearAlgebra
end OAI
