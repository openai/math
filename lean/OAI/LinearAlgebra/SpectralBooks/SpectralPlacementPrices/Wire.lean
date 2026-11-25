import OAI.LinearAlgebra.SpectralBooks.Prices
import OAI.LinearAlgebra.SpectralBooks.Sector

/-! # Finite spectral wire bounds on a metric spectral space

The four endpoints and the two intermediate points fit into a single finite
placement. Its normalized spectral point measures every pairwise distance at
the same scale, even when some of the six sites coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SpectralPlacementPrices

open SiteTensor

variable {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)

include P in
/-- A synchronized wire inequality for finite spectral points implies Busemann
convexity of every metric space carrying their placement prices. -/
theorem sectorBusemann_of_rawWireDistance
    (h : ∀ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 6) K → _ → Prop))
      (c : ℝ), 0 ≤ c → ∀ a b a' b' z w : Fin 6, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      let d := rawWireDistance φ c
      d a z = u * d a b → d z b = (1-u) * d a b →
      d a' w = u * d a' b' → d w b' = (1-u) * d a' b' →
      d z w ≤ (1-u) * d a a' + u * d b b') : SectorBusemann X := by
  intro a b a' b' z w u hu hz hw
  let p : Fin 6 → X := ![a,b,a',b',z,w]
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have wire (i j : Fin 6) : P.price W (p ∘ ![i,j]) = dist (p i) (p j) := P.wire _
  rcases P.zero_or_common_group_price p with hzero | ⟨φ, c, hc, hp⟩
  · have hd (i j : Fin 6) : dist (p i) (p j) = 0 := (wire i j).symm.trans (hzero W ![i,j])
    change dist (p 4) (p 5) ≤ (1-u) * dist (p 0) (p 2) + u * dist (p 1) (p 3)
    simp only [hd, mul_zero, add_zero, le_refl]
  · have hd (i j : Fin 6) : rawWireDistance φ c i j = dist (p i) (p j) :=
      (hp W ![i,j]).symm.trans (wire i j)
    have hh := h φ c hc.le 0 1 2 3 4 5 u hu
    simp only [hd] at hh
    exact hh hz.1 hz.2 hw.1 hw.2

end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
