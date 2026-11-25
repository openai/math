import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Nodes
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.OneIndexRelocation
import OAI.LinearAlgebra.SpectralBooks.IndependentRelocation
import OAI.LinearAlgebra.SpectralBooks.Coupling

/-! # Independent relocation at a wire split node

Applying the one-index inequality successively to its free index and its
second mark bounds the node's cost by the product mean of its four corners.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor.Relocation.WireNode

open Function

variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}

/-- The constant inherited wire offset passes unchanged through interpolation. -/
theorem independent (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop))
    (c : ℝ) (hc : 0 ≤ c) (N : WireNode K J Q) (A B : Fin 2 → J) (z w : J)
    (u v : ℝ) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c (A 0) z = u * rawWireDistance φ c (A 0) (A 1))
    (hz₁ : rawWireDistance φ c z (A 1) = (1-u) * rawWireDistance φ c (A 0) (A 1))
    (hw₀ : rawWireDistance φ c (B 0) w = v * rawWireDistance φ c (B 0) (B 1))
    (hw₁ : rawWireDistance φ c w (B 1) = (1-v) * rawWireDistance φ c (B 0) (B 1)) :
    cost φ c N z w ≤ EndpointTable.cost (EndpointTable.independent u v)
      (fun i j ↦ cost φ c N (A i) (B j)) := by
  classical
  let T := marked N.A (Fin Q) N.T
  let site p y := placeMark (update N.site N.other y) p
  have row (p y k : J) : update (site p y) (.inr ()) k = site k y := by
    funext j
    rcases j with j | ⟨⟩
    · exact update_of_ne (by simp) _ _
    · exact update_self ..
  have col (p y k : J) : update (site p y) (.inl N.other) k = site p k := by
    funext j
    rcases j with j | ⟨⟩
    · by_cases hj : j = N.other
      · subst j
        rw [update_self]
        exact (update_self N.other k N.site).symm
      · rw [update_of_ne (fun h ↦ hj (Sum.inl.inj h))]
        change update N.site N.other y j = update N.site N.other k j
        rw [update_of_ne hj, update_of_ne hj]
    · exact update_of_ne (by simp) _ _
  rw [EndpointTable.cost_independent]
  apply independent_relocation_two (cost φ c N) _ _ _ _ _ _ hu
  · intro y
    have h := rawLogPrice_relocate φ c hc T (site z y) (.inr ()) (A 0) z (A 1) u hu
      ((rawWireDistance_symm φ c z (A 0)).trans hz₀) hz₁
    simp only [row] at h
    change rawLogPrice φ c (T.group (site z y)) - N.offset ≤
      (1-u) * (rawLogPrice φ c (T.group (site (A 0) y)) - N.offset) +
      u * (rawLogPrice φ c (T.group (site (A 1) y)) - N.offset)
    linarith only [h]
  · intro p
    have h := rawLogPrice_relocate φ c hc T (site p w) (.inl N.other) (B 0) w (B 1) v hv
      ((rawWireDistance_symm φ c w (B 0)).trans hw₀) hw₁
    simp only [col] at h
    change rawLogPrice φ c (T.group (site p w)) - N.offset ≤
      (1-v) * (rawLogPrice φ c (T.group (site p (B 0))) - N.offset) +
      v * (rawLogPrice φ c (T.group (site p (B 1))) - N.offset)
    linarith only [h]

end SiteTensor.Relocation.WireNode

end

end SpectralBooks
end LinearAlgebra
end OAI
