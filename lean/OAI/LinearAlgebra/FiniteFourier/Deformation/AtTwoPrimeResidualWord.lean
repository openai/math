import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeResidual
import OAI.LinearAlgebra.FiniteFourier.AtTwoEndpointBlocks

/-! # Uniform depth of the residual prime-axis transforms

The zero-frequency block has three rows and the other blocks have two
rows. Elimination on all fibers simultaneously uses 82 layers, including
after extending scalars from the cyclotomic coefficient ring to a jet.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix

variable {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S]
  {p : ℕ} [Fact p.Prime] {C : PrimeAxisCosets p} {u : Rˣ} {hp7 : 7 ≤ p}
  (F : AtTwoPrimeFactor R C u hp7) (hpu : IsUnit (p : R))
  (hm : IsUnit (((p-1)/2 : ℕ) : R)) (hu : u^((p-1)/2) = 1)
  (hs : ∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))

/-- Both residual conversions, including mixed scalar/active rows at frequency
zero, have uniformly bounded words in every semilocal target with unit splitting. -/
theorem primeAxisResidual_layerWords (φ : R →+* S) [Finite (MaximalSpectrum S)]
    (hunit : ∀ x : S, ∃ t, IsUnit t ∧ IsUnit (x-t)) :
    LayerWord 82 ((primeAxisResidual F hpu hm hu hs).map φ) ∧
    LayerWord 82 ((primeAxisResidualInv F hpu hm hu hs).map φ) := by
  let M := primeAxisResidual F hpu hm hu hs
  let N := primeAxisResidualInv F hpu hm hu hs
  have hMN : M * N = 1 := primeAxisResidual_mul_inv F hpu hm hu hs
  have hNM : N * M = 1 := primeAxisResidualInv_mul F hpu hm hu hs
  have hM : IsUnit M := ⟨⟨M,N,hMN,hNM⟩,rfl⟩
  have hN : IsUnit N := ⟨⟨N,M,hNM,hMN⟩,rfl⟩
  have hmpos : 0 < (p-1)/2 := by omega
  have hcard (j : Fin ((p-1)/2)) : Fintype.card {i // primeAxisFrequency hmpos i = j} ≤ 3 := by
    rw [card_primeAxisFrequency]; split <;> decide
  constructor
  · apply layerWord_semilocal_blocks hunit (primeAxisFrequency hmpos) (b := 3) _
      (hM.map φ.mapMatrix) _ hcard
    intro i j h
    change φ (primeAxisResidual F hpu hm hu hs i j) = 0
    rw [primeAxisResidual_sparse _ _ _ _ _ i j h, map_zero]
  · apply layerWord_semilocal_blocks hunit (primeAxisFrequency hmpos) (b := 3) _
      (hN.map φ.mapMatrix) _ hcard
    intro i j h
    change φ (primeAxisResidualInv F hpu hm hu hs i j) = 0
    rw [primeAxisResidualInv_sparse _ _ _ _ _ i j h, map_zero]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
