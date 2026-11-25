import OAI.LinearAlgebra.SpectralBooks.IncrementEmbedding
import OAI.LinearAlgebra.SpectralBooks.IncrementFieldTransfer
import OAI.LinearAlgebra.SpectralBooks.IncrementLimit
import OAI.LinearAlgebra.SpectralBooks.IncrementRestriction
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonalPrice
import OAI.LinearAlgebra.SpectralBooks.PlacementDiagonal
import OAI.LinearAlgebra.SpectralBooks.SpectralSublevels

/-! # Intersecting submodularity at a spectral placement

The four partial diagonals are evaluated by a single point of the tensor
spectrum on the same placement. We apply the finite common-label degeneration
at that point, eliminate its linear label overhead and telescope.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal

section

open SiteTensor

variable {K X : Type*} [Field K] [PseudoMetricSpace X]

/-- In every characteristic, the diagonal prices in a spectral space are
intersecting submodular (Lemma `lem:submod`). -/
theorem SpectralPlacementPrices.intersectingSubmodular
    (P : SpectralPlacementPrices K X) [DecidableEq X] :
    IntersectingSubmodular P.diagonal := by
  classical
  apply intersectingSubmodular_iff_diminishingIncrements.mpr
  intro I A z hI hIA hz
  let k := I.card - 1
  let m := (A \ I).card
  obtain ⟨e, hj, ho, ha, hu⟩ := exists_incrementSite_embedding hI hIA hz
  have hcard := Finset.card_pos.mpr hI
  have hk : k + 1 = I.card := by dsimp [k]; omega
  have hjne : (incrementJointMask k m).Nonempty := ⟨.inl 0, by simp [incrementJointMask]⟩
  have hone : (incrementOldMask k m).Nonempty := ⟨.inl 0, by simp [incrementOldMask]⟩
  have hane : (incrementAuxMask k m).Nonempty := Finset.insert_nonempty _ _
  have hune : (Finset.univ : Finset (IncrementSite k m)).Nonempty := Finset.univ_nonempty
  obtain ⟨φ, c, hc, hd⟩ := P.exists_point_diagonal_map e
  apply priceIncrement_of_finite_diagonal hcard (P.diagonal_nonneg _)
  intro q hq
  let L := 2 * (k+1) * (q-1) + 1
  have hqpos : 0 < q := by omega
  have hL : 0 < L := Nat.zero_lt_succ _
  let D (S : Finset (IncrementSite k m)) (n : ℕ) :=
    (φ.val (ofRaw (Raw.maskDiagonal K S (Fin n))) : ℝ)
  have hD (S : Finset (IncrementSite k m)) (hs : S.Nonempty) (n : ℕ) (hn : 0 < n) :
      0 < D S n := by
    let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
    have h := φ.property.2.2.2.2 _ _
      (show (1 : TensorClass.{0} (IncrementSite k m) K) ≤ ofRaw (Raw.maskDiagonal K S (Fin n)) from
        Raw.one_restricts_of_nonzero _ (Raw.maskDiagonal_ne_zero S hs (Fin n)))
    rw [φ.property.2.1] at h
    exact_mod_cast zero_lt_one.trans_le h
  have comp := commonLabel_value_le K q k m φ
  unfold coeffValue at comp
  rw [ofCoeffs_incrementTargetBasis, ofCoeffs_incrementSourceBasis,
    φ.property.2.2.2.1, φ.property.2.2.2.1] at comp
  have hr : D Finset.univ q * D (incrementJointMask k m) q ≤
      D (incrementOldMask k m) q * D (incrementAuxMask k m) L := by exact_mod_cast comp
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (mul_pos (hD _ hune q hqpos) (hD _ hjne q hqpos)) hr
  rw [Real.logb_mul (hD _ hune _ hqpos).ne' (hD _ hjne _ hqpos).ne',
    Real.logb_mul (hD _ hone _ hqpos).ne' (hD _ hane _ hL).ne'] at hlog
  have hp (S : Finset (IncrementSite k m)) (hs : S.Nonempty) (n : ℕ) (hn : 0 < n) :
      c * Real.logb 2 (D S n) = P.diagonal (S.map e) * Real.logb 2 n := by
    dsimp only [D]
    rw [maskDiagonal_log_price φ S hs hn, hd S hs, mul_assoc]
  have res := mul_le_mul_of_nonneg_left hlog hc
  rw [mul_add, mul_add, hp _ hune _ hqpos, hp _ hjne _ hqpos, hp _ hone _ hqpos,
    hp _ hane _ hL, hu, hj, ho, ha, ← add_mul] at res
  simpa only [L, hk] using res

/-- Equation `eq:width-increment` for the cost of adjoining one new site. -/
theorem SpectralPlacementPrices.diminishingIncrements
    (P : SpectralPlacementPrices K X) [DecidableEq X] : DiminishingIncrements P.diagonal :=
  intersectingSubmodular_iff_diminishingIncrements.mp P.intersectingSubmodular

end

end SpectralBooks
end LinearAlgebra
end OAI
