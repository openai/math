import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateReindex

/-! # Endpoint factorization in the original work-row coordinates

The source and destination charts are chosen independently. Conjugating
each endpoint by its own chart keeps it independent of the opposite label.
Only the middle map involves both changes of coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K : Type*} [CommSemiring K] {I O X : Type} [Fintype I] [Fintype O] [Fintype X]
variable {M : Matrix X X K} {source : Matrix I I K} {dest : Matrix O O K} {mid : Matrix O I K}

/-- Transport a three-factor endpoint identity to the original index type. -/
theorem endpointFactor_reindex (x : I ≃ X) (z : O ≃ X)
    (h : M.submatrix z x = dest * (mid * source)) :
    M = Matrix.reindex z z dest * Matrix.reindex z x mid * Matrix.reindex x x source := by
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.mul_assoc, ← h]
  ext o i
  simp

/-- Both endpoint programs keep their own call budgets under transport, and
the rectangular middle circuit keeps its local gate count. -/
theorem endpointFactor_reindex_programs {ℓ f F ci si co so cm : ℕ} {ζ : K}
    (x : I ≃ X) (z : O ≃ X) (h : M.submatrix z x = dest * (mid * source))
    (hs : PrimeTemplateProgram ℓ f F ζ source ci si)
    (hd : PrimeTemplateProgram ℓ f F ζ dest co so) (hm : RealizableAtMost mid cm) :
    M = Matrix.reindex z z dest * Matrix.reindex z x mid * Matrix.reindex x x source ∧
      PrimeTemplateProgram ℓ f F ζ (Matrix.reindex x x source) ci si ∧
      PrimeTemplateProgram ℓ f F ζ (Matrix.reindex z z dest) co so ∧
      RealizableAtMost (Matrix.reindex z x mid) cm :=
  ⟨endpointFactor_reindex x z h, hs.reindex x x, hd.reindex z z, hm.reindex z x⟩

end FiniteFourier
end LinearAlgebra
end OAI
