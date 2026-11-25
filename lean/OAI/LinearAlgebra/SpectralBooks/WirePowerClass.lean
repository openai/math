import OAI.LinearAlgebra.SpectralBooks.BasisSumClass
import OAI.LinearAlgebra.SpectralBooks.WireCutRank
import OAI.LinearAlgebra.SpectralBooks.MaskDiagonal
import OAI.LinearAlgebra.SpectralBooks.GroupedPower
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Diagonal

/-!
# Restriction classes of direct sums of wire powers

The source of the local linear maps in the crossing construction has one copy
tag at each site, one wire tag per factor, and one equality string for each
selected wire. These coefficient coordinates give the multiple of a semiring
power that occurs in strict spectral comparison.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace Crossing

open SiteTensor

variable {I : Type*} [Fintype I] [Nonempty I] (F : Type*) [Field F]

/-- Tagging every local basis with a common copy index realizes an additive
multiple of the restriction class. -/
theorem ofRaw_copiesBasis {S : Type} [Fintype S] {A : I → Type} [∀ i, Fintype (A i)]
    (term : S → ∀ i, A i) (k : ℕ) :
    ofRaw (I := I) (K := F) ⟨fun i ↦ Fin k × A i, fun _ ↦ inferInstance,
      basisTensor (copiesBasis term k)⟩ =
      k • ofRaw (I := I) (K := F) ⟨A, inferInstance, basisTensor term⟩ := by
  have h := basisTensor_paired_eq_mul (K := F) (fun (r : Fin k) (_ : I) ↦ r) term
    (copiesBasis term k) (fun i ↦ Equiv.refl (Fin k × A i)) (fun _ _ _ ↦ rfl)
  rw [h, nsmul_eq_mul, ← ofRaw_diagonal_fin_eq_natCast I F k]
  congr 1
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (fun _ ↦ Equiv.refl (Fin k))
  intro x
  simp only [basisTensor, Raw.diagonal]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> first | rfl | contradiction

/-- Choosing a basis term independently in each of the copies realizes the
semiring tensor power. -/
theorem ofRaw_powerBasis {S : Type} [Fintype S] {A : I → Type} [∀ i, Fintype (A i)]
    (term : S → ∀ i, A i) (j : ℕ) :
    ofRaw (I := I) (K := F) ⟨fun i ↦ Fin j → A i, fun _ ↦ inferInstance,
      basisTensor (powerBasis term j)⟩ =
      ofRaw (I := I) (K := F) ⟨A, inferInstance, basisTensor term⟩ ^ j := by
  have he : basisTensor (F := F) (powerBasis term j) = groupedPower j (basisTensor term) :=
    funext (basisTensor_power term j)
  rw [he, ofRaw_groupedPower]

/-- The concrete local-coordinate source in strict spectral comparison is
the indicated additive multiple of the power of the sum of wire classes. -/
theorem ofRaw_copiesOfWirePower {E : Type} [Fintype E] (wires : E → Wire I) (k j : ℕ) :
    ofRaw (I := I) (K := F) ⟨fun i ↦ Fin k × (Fin j → Σ e, (wires e).Leg i),
      fun _ ↦ inferInstance, copiesOfWirePower (F := F) wires k j⟩ =
      k • (∑ e, ofRaw ((wires e).raw F)) ^ j := by
  rw [copiesOfWirePower, ofRaw_copiesBasis, ofRaw_powerBasis]
  exact congrArg (fun z : TensorClass.{0} I F ↦ k • z ^ j)
    (SiteTensor.ofRaw_sumBasis (I := I) (A := fun e ↦ (wires e).Leg) (K := F) (fun e ↦ (wires e).basisTerm))

end Crossing

end SpectralBooks
end LinearAlgebra
end OAI
