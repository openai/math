import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Counting transvections in block elimination

Isolating a final coordinate with at most four transvections per remaining
coordinate gives a quadratic bound on the full diagonal factorization.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Matrix.TransvectionStruct

variable {R : Type*} [CommRing R]

private def BoundedDiagonalReduction {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I R) (bound : ℕ) : Prop :=
  ∃ (L L' : List (TransvectionStruct I R)) (D : I → R), L.length + L'.length ≤ bound ∧
    (L.map toMatrix).prod * M * (L'.map toMatrix).prod = diagonal D

private theorem boundedReduction_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (M : Matrix I I R) {bound : ℕ}
    (h : BoundedDiagonalReduction (reindexAlgEquiv R _ e M) bound) :
    BoundedDiagonalReduction M bound := by
  obtain ⟨L, L', D, hlen, hD⟩ := h
  refine ⟨L.map (reindexEquiv e.symm), L'.map (reindexEquiv e.symm), D ∘ e, by simpa, ?_⟩
  have he : M = reindexAlgEquiv R _ e.symm (reindexAlgEquiv R _ e M) := by simp
  rw [he]
  simp_rw [List.map_map, toMatrix_reindexEquiv_prod, ← map_mul, hD]
  simp

private theorem boundedReduction_block {n b : ℕ}
    (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R)
    (L L' : List (TransvectionStruct (Fin n ⊕ Unit) R))
    (h : IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod))
    (ih : ∀ N : Matrix (Fin n) (Fin n) R, BoundedDiagonalReduction N b) :
    BoundedDiagonalReduction M (b + (L.length + L'.length)) := by
  let N := (L.map toMatrix).prod * M * (L'.map toMatrix).prod
  obtain ⟨A, B, D, hab, hD⟩ := ih (toBlocks₁₁ N)
  let c := N (.inr ()) (.inr ())
  refine ⟨A.map (sumInl Unit) ++ L, L' ++ B.map (sumInl Unit),
    Sum.elim D (fun _ => c), ?_, ?_⟩
  · simp only [List.length_append, List.length_map]
    omega
  · suffices (A.map (toMatrix ∘ sumInl Unit)).prod * N *
        (B.map (toMatrix ∘ sumInl Unit)).prod = diagonal (Sum.elim D fun _ => c) by
      simpa [N, Matrix.mul_assoc] using this
    have hN : N = fromBlocks (toBlocks₁₁ N) 0 0 (diagonal fun _ => c) := by
      conv_lhs => rw [← fromBlocks_toBlocks N, h.1, h.2]
      rfl
    conv_lhs => rw [hN]
    simp [hD]

/-- A uniform bound of `4 * n` on isolating the last block in dimension `n + 1`
gives a diagonal factorization by at most twice the square of the dimension
many elementary shears. -/
theorem exists_bounded_diagonal_shear_factorization_of_block_step
    (step : ∀ (n : ℕ) (M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R),
      ∃ L L' : List (TransvectionStruct (Fin n ⊕ Unit) R), L.length + L'.length ≤ 4 * n ∧
        IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (L'.map toMatrix).prod))
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I R) :
    ∃ (L L' : List (TransvectionStruct I R)) (D : I → R),
      L.length + L'.length ≤ 2 * (Fintype.card I) ^ 2 ∧
      M = (L.map toMatrix).prod * diagonal D * (L'.map toMatrix).prod := by
  have reduce (k : ℕ) (N : Matrix (Fin k) (Fin k) R) : BoundedDiagonalReduction N (2 * k ^ 2) := by
    induction k with
    | zero => exact ⟨[], [], fun _ => 0, by simp, Matrix.ext fun i => i.elim0⟩
    | succ n ih =>
      let e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fintype.equivOfCardEq (by simp)
      apply boundedReduction_reindex e N
      let P := reindexAlgEquiv R _ e N
      obtain ⟨L, L', hlen, hblock⟩ := step n P
      obtain ⟨A, B, D, hab, hD⟩ := boundedReduction_block P L L' hblock ih
      refine ⟨A, B, D, ?_, hD⟩
      simp only [pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at hab ⊢
      omega
  have e := Fintype.equivFin I
  obtain ⟨L, L', D, hlen, hD⟩ := boundedReduction_reindex e M
    (reduce _ (reindexAlgEquiv R _ e M))
  refine ⟨L.reverse.map TransvectionStruct.inv, L'.reverse.map TransvectionStruct.inv, D,
    by simpa, ?_⟩
  suffices M = (L.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod * (L.map toMatrix).prod *
      M * ((L'.map toMatrix).prod * (L'.reverse.map (toMatrix ∘ TransvectionStruct.inv)).prod) by
    simpa [← hD, Matrix.mul_assoc] using this
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, Matrix.one_mul, Matrix.mul_one]

end FiniteFourier
end LinearAlgebra
end OAI
