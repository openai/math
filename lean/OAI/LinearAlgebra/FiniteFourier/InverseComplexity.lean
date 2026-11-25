import OAI.LinearAlgebra.FiniteFourier.CharacterBasis
import OAI.LinearAlgebra.FiniteFourier.CircuitReindex

/-! # Complexity of the inverse character transform

Choose a symmetric identification with the character group. The inverse matrix
is then the forward matrix with permuted indices and a common output scaling,
both free in the binary linear circuit model.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable (G K : Type*) [AddCommGroup G] [Fintype G] [Field K]

/-- Symmetric self-duality reindexes the inverse into a scalar multiple of the forward matrix. -/
theorem exists_reindex_inverseFourierMatrix (h : Admissible G K) :
    ∃ (R : Character G K ≃ G) (E : G ≃ Character G K), inverseFourierMatrix G K =
      (Fintype.card G : K)⁻¹ • Matrix.reindex R E (fourierMatrix G K) := by
  obtain ⟨e, hs⟩ := exists_symmetric_character_equiv G K h
  let E : G ≃ Character G K := Multiplicative.ofAdd.trans e.toEquiv
  let R : Character G K ≃ G := E.symm.trans (Equiv.neg G)
  refine ⟨R, E, ?_⟩
  ext g χ
  change _ * (χ (Multiplicative.ofAdd (-g)) : K) =
      _ * ↑(E (-g) (Multiplicative.ofAdd (E.symm χ)))
  congr 1
  conv_lhs => rw [← E.apply_symm_apply χ]
  exact congrArg Units.val (hs (E.symm χ) (-g))

/-- Equality of the forward and inverse minimum gate counts. -/
theorem complexity_inverseFourierMatrix (h : Admissible G K) :
    complexity (inverseFourierMatrix G K) = complexity (fourierMatrix G K) := by
  obtain ⟨R, E, he⟩ := exists_reindex_inverseFourierMatrix G K h
  rw [he, complexity_smul _ (inv_ne_zero h.1), complexity_reindex]

end FiniteFourier
end LinearAlgebra
end OAI
