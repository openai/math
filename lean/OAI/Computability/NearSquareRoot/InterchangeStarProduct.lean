import OAI.Computability.NearSquareRoot.InterchangeStarFactors

/-!
# Reconstructing an address map from star elimination

Row and column elimination gives a diagonal matrix. Undoing its transvections
in reverse order preserves the partition into batches with one common endpoint.
For a nonsingular address change, the resulting diagonal scalings are nonzero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix Matrix.TransvectionStruct

variable {I : Type*}

private abbrev T (I : Type*) := Matrix.TransvectionStruct I ℚ

private def undoBatch (s : List (T I)) := s.reverse.map TransvectionStruct.inv

private def undoBatches (L : List (List (T I))) := L.reverse.map undoBatch

private theorem flatten_undoBatches (L : List (List (T I))) :
    (undoBatches L).flatten = L.flatten.reverse.map TransvectionStruct.inv := by
  rw [List.reverse_flatten, List.map_flatten]
  simp only [undoBatches, List.map_reverse, List.map_map, Function.comp_def]
  congr 3
  funext s
  exact List.map_reverse

private theorem undoBatches_mem {P : List (T I) → Prop}
    (hP : ∀ s, P s → P (undoBatch s))
    {L : List (List (T I))} (hL : ∀ s ∈ L, P s) :
    ∀ s ∈ undoBatches L, P s := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hP t (hL t (List.mem_reverse.mp ht))

private theorem isStar_undoBatch {s : List (T I)} (hs : IsStar s) : IsStar (undoBatch s) := by
  obtain ⟨i, hi⟩ | ⟨j, hj⟩ := hs
  · left
    refine ⟨i, fun t ht => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact hi a (List.mem_reverse.mp ha)
  · right
    refine ⟨j, fun t ht => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
    exact hj a (List.mem_reverse.mp ha)

variable [Fintype I] [DecidableEq I]

/-- Undo an elimination and preserve the number of batches. -/
private theorem product_of_diagonalization
    (M : Matrix I I ℚ) (L R : List (List (T I))) (D : I → ℚ)
    (he : (L.flatten.map toMatrix).prod * M * (R.flatten.map toMatrix).prod = diagonal D) :
    M = ((undoBatches L).flatten.map toMatrix).prod * diagonal D *
      ((undoBatches R).flatten.map toMatrix).prod := by
  simp only [flatten_undoBatches, List.map_map]
  rw [← he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, reverse_inv_prod_mul_prod, one_mul,
    Matrix.mul_assoc, prod_mul_reverse_inv_prod, mul_one]

/-- An invertible matrix can only have nonzero scalings in such a factorization. -/
theorem star_diagonal_ne_zero {M : Matrix I I ℚ} {L R : List (List (T I))} {D : I → ℚ}
    (hM : M.det ≠ 0) (he : M = (L.flatten.map toMatrix).prod * diagonal D *
      (R.flatten.map toMatrix).prod) : ∀ i, D i ≠ 0 := by
  have hd : (∏ i, D i) ≠ 0 := by
    simpa only [he, det_mul, det_toMatrix_prod, det_diagonal, one_mul, mul_one] using hM
  simpa only [Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies] using hd

/-- Every rational address matrix is a diagonal between two lists of star batches.
The combined batch count is at most three per address field. An invertible
input yields invertible scalings at every coordinate. -/
theorem factor_stars (M : Matrix I I ℚ) :
    ∃ (L R : List (List (Matrix.TransvectionStruct I ℚ))) (D : I → ℚ),
      (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧
      L.length + R.length ≤ 3 * Fintype.card I ∧
      M = (L.flatten.map toMatrix).prod * diagonal D * (R.flatten.map toMatrix).prod ∧
      (IsUnit M → ∀ i, D i ≠ 0) := by
  obtain ⟨L, R, D, hL, hR, hb, he⟩ := diagonalize_stars M
  have hf := product_of_diagonalization M L R D he
  refine ⟨undoBatches L, undoBatches R, D, undoBatches_mem (P := IsStar) (fun _ => isStar_undoBatch) hL,
    undoBatches_mem (P := IsStar) (fun _ => isStar_undoBatch) hR, ?_, hf, ?_⟩
  · simpa only [undoBatches, List.length_map, List.length_reverse] using hb
  · intro hM
    exact star_diagonal_ne_zero ((hM.map Matrix.detMonoidHom).ne_zero) hf

end Interchange

end NearSquareRoot
end Computability
end OAI
