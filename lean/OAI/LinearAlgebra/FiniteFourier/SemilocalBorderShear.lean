import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Factoring border shears

A block matrix with identity diagonal and one off-diagonal row or column is
a product of at most one elementary transvection per entry of that border.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

private theorem exists_border_word {B : Type*} [AddCommMonoid B]
    (block : B → Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R) (hzero : block 0 = 1)
    (hadd : ∀ x y, block (x + y) = block x * block y)
    (v : Fin n → B) (t : Fin n → TransvectionStruct (Fin n ⊕ Unit) R)
    (ht : ∀ i, (t i).toMatrix = block (v i)) :
    ∃ l : List (TransvectionStruct (Fin n ⊕ Unit) R), l.length ≤ n ∧
      (l.map TransvectionStruct.toMatrix).prod = block (∑ i, v i) := by
  have partial_word (s : Finset (Fin n)) :
      ∃ l : List (TransvectionStruct (Fin n ⊕ Unit) R), l.length = s.card ∧
        (l.map TransvectionStruct.toMatrix).prod = block (∑ i ∈ s, v i) := by
    induction s using Finset.induction with
    | empty => exact ⟨[], by simp, by simp [hzero]⟩
    | insert i s his ih =>
      obtain ⟨l, hl, he⟩ := ih
      exact ⟨t i :: l, by simp [hl, his], by simp [he, ht, his, hadd]⟩
  obtain ⟨l, hl, he⟩ := partial_word Finset.univ
  exact ⟨l, by simpa using hl.le, he⟩

/-- Add a multiple of the last coordinate to each of the preceding coordinates. -/
theorem exists_border_upper_transvections (v : Matrix (Fin n) Unit R) :
    ∃ l : List (TransvectionStruct (Fin n ⊕ Unit) R), l.length ≤ n ∧
      (l.map TransvectionStruct.toMatrix).prod = fromBlocks 1 v 0 1 := by
  let t (i : Fin n) : TransvectionStruct (Fin n ⊕ Unit) R :=
    ⟨.inl i, .inr (), by simp, v i ()⟩
  let block (w : Matrix (Fin n) Unit R) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
    fromBlocks 1 w 0 1
  have hs : ∑ i, single i () (v i ()) = v := by simpa using (matrix_eq_sum_single v).symm
  have ht (i : Fin n) : (t i).toMatrix = block (single i () (v i ())) := by
    ext (a | a) (b | b) <;> simp [t, block, transvection, single_apply, one_apply]
  simpa [hs, block] using exists_border_word block (by simp [block])
    (by simp [block, fromBlocks_multiply, add_comm]) (fun i => single i () (v i ())) t ht

/-- A shear supported in the bottom border is a product of at most one transvection per column. -/
theorem exists_border_lower_transvections (v : Matrix Unit (Fin n) R) :
    ∃ l : List (Matrix.TransvectionStruct (Fin n ⊕ Unit) R), l.length ≤ n ∧
      (l.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.fromBlocks 1 0 v 1 := by
  classical
  let block (x : Matrix Unit (Fin n) R) : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R :=
    Matrix.fromBlocks 1 0 x 1
  let t (i : Fin n) : Matrix.TransvectionStruct (Fin n ⊕ Unit) R :=
    ⟨Sum.inr (), Sum.inl i, by simp, v () i⟩
  have ht (i : Fin n) : (t i).toMatrix = block (Matrix.single () i (v () i)) := by
    ext a b
    cases a <;> cases b <;> simp [t, block, Matrix.transvection, Matrix.single_apply, Matrix.one_apply]
  have hv : (∑ i, Matrix.single () i (v () i)) = v := by
    ext a b
    cases a
    simp [Matrix.sum_apply, Matrix.single_apply]
  simpa [hv, block] using exists_border_word block (by simp [block])
    (by simp [block, Matrix.fromBlocks_multiply]) (fun i => Matrix.single () i (v () i)) t ht

end FiniteFourier
end LinearAlgebra
end OAI
