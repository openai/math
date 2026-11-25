import OAI.LinearAlgebra.SpectralBooks.Prices
import OAI.LinearAlgebra.SpectralBooks.SpectralFlatLaw

/-! # From normalized finite relocation to synchronized diagonal convexity

All three placements of a binary diagonal and all wires measuring the
individual motions are evaluated by one common normalized spectral point.
The finite alphabet may list the same metric site more than once.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open HyperbolicObstruction Set
open scoped Classical

section

/-- The synchronized diagonal case of finite many-index relocation. -/
def SiteTensor.RawDiagonalJointConvexity (K : Type*) [Field K] : Prop :=
  ∀ {J : Type} [Fintype J] [Nonempty J]
    (φ : normalizedSpectrum ((· ≤ ·) : SiteTensor.TensorClass.{0} J K → _ → Prop))
    (c : ℝ), 0 < c → ∀ (r : ℕ) [NeZero r] (a z b : Fin r → J) (t : ℝ),
    t ∈ Icc (0 : ℝ) 1 →
    (∀ i, SiteTensor.rawWireDistance φ c (z i) (a i) = t * SiteTensor.rawWireDistance φ c (a i) (b i)) →
    (∀ i, SiteTensor.rawWireDistance φ c (z i) (b i) = (1-t) * SiteTensor.rawWireDistance φ c (a i) (b i)) →
    SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group z) ≤
      (1-t) * SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group a) +
      t * SiteTensor.rawLogPrice φ c ((SiteTensor.Raw.diagonal (Fin r) K (Fin 2)).group b)

namespace SpectralPlacementPrices

open SiteTensor

variable {K : Type*} {X : Type} [Field K] [MetricSpace X]

/-- A common fraction of the endpoint distance at every mark gives the
synchronized bound. No ambient geodesic selection is needed. -/
theorem price_binaryDiagonal_le_of_fraction (P : SpectralPlacementPrices K X)
    (hraw : RawDiagonalJointConvexity K) {I : Type} [Fintype I] [Nonempty I] (p m q : I → X)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : ∀ i, dist (m i) (p i) = t * dist (p i) (q i))
    (hq : ∀ i, dist (m i) (q i) = (1-t) * dist (p i) (q i)) :
    P.price (Raw.diagonal I K (Fin 2)) m ≤
      (1-t) * P.price (Raw.diagonal I K (Fin 2)) p + t * P.price (Raw.diagonal I K (Fin 2)) q := by
  let r := Fintype.card I
  let : NeZero r := ⟨Fintype.card_ne_zero⟩
  let e : Fin r ≃ I := (Fintype.equivFin I).symm
  let points (v : Fin r × Fin 3) := ![p (e v.1), m (e v.1), q (e v.1)] v.2
  let atLabel (k : Fin 3) (j : Fin r) : Fin r × Fin 3 := (j, k)
  let T := Raw.diagonal (Fin r) K (Fin 2)
  have hrelabel (v : I → X) : P.price T (v ∘ e) = P.price (Raw.diagonal I K (Fin 2)) v := by
    rw [P.price_binaryDiagonal_eq, P.price_binaryDiagonal_eq,
      ← Finset.image_image, Finset.image_univ_equiv]
  rw [← hrelabel m, ← hrelabel p, ← hrelabel q]
  change P.price T (points ∘ atLabel 1) ≤
    (1-t) * P.price T (points ∘ atLabel 0) + t * P.price T (points ∘ atLabel 2)
  rcases P.zero_or_common_group_price points with hzero | ⟨φ, c, hc, hprice⟩
  · simp only [hzero, mul_zero, add_zero, le_refl]
  · have hd (x y : Fin r × Fin 3) : rawWireDistance φ c x y = dist (points x) (points y) :=
      (hprice (Raw.diagonal (Fin 2) K (Fin 2)) ![x,y]).symm.trans (P.wire _)
    simp only [hprice]
    apply hraw φ c hc r (atLabel 0) (atLabel 1) (atLabel 2) t ht
    · intro i
      rw [hd, hd]
      change dist (m (e i)) (p (e i)) = t * dist (p (e i)) (q (e i))
      exact hp (e i)
    · intro i
      rw [hd, hd]
      exact hq (e i)

/-- Normalized finite-site relocation gives synchronized geodesic convexity
for a placed binary diagonal with any nonempty finite index set. -/
theorem jointlyConvexDiagonal_of_raw (P : SpectralPlacementPrices K X) (hX : CATZero X)
    (hraw : RawDiagonalJointConvexity K) : P.JointlyConvexDiagonal hX := by
  intro I _ _ p q t ht
  apply P.price_binaryDiagonal_le_of_fraction hraw p _ q t ht
  · intro i
    rw [dist_comm]
    exact CATZero.segment_left hX _ _ ht
  · exact fun i ↦ CATZero.segment_right hX _ _ ht

end SpectralPlacementPrices
end

end

end SpectralBooks
end LinearAlgebra
end OAI
