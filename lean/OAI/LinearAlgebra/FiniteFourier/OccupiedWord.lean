import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Words that restore occupied workspace

The lower-right identity block requires the workspace to be returned with its
original value on every input. Products can reuse the same workspace.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix
variable {K : Type*} [CommSemiring K] {I J W : Type}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]

/-- A word on the data registers and an auxiliary array with arbitrary contents. -/
abbrev OccupiedWord (W : Type) [Fintype W] [DecidableEq W] (d : ℕ) (A : Matrix I I K) : Prop :=
  LayerWord d (fromBlocks A 0 0 (1 : Matrix W W K))

theorem LayerWord.occupied {d : ℕ} {A : Matrix I I K} (h : LayerWord d A) :
    OccupiedWord W d A := layerWord_parallel h (layerWord_one _)

theorem OccupiedWord.mul {d e : ℕ} {A B : Matrix I I K}
    (hA : OccupiedWord W d A) (hB : OccupiedWord W e B) : OccupiedWord W (d+e) (A*B) := by
  simpa only [fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul,
    zero_add, add_zero] using layerWord_mul hA hB

theorem OccupiedWord.relabel {d : ℕ} {A : Matrix I I K} (h : OccupiedWord W d A) (e : I ≃ J) :
    OccupiedWord W d (A.submatrix e.symm e.symm) := by
  have h' := LayerWord.relabel h (e.sumCongr (Equiv.refl W))
  convert h' using 1
  ext (i | i) (j | j) <;> rfl

theorem OccupiedWord.assoc {d : ℕ} {A : Matrix I I K}
    (h : OccupiedWord W d (fromBlocks A 0 0 (1 : Matrix J J K))) :
    OccupiedWord (J ⊕ W) d A := by
  have h' := LayerWord.relabel h (Equiv.sumAssoc I J W)
  convert h' using 1
  ext i j
  rcases i with i | (j₁|w) <;> rcases j with k | (l|v) <;>
    simp [fromBlocks, Matrix.submatrix, Matrix.one_apply]

theorem occupiedWord_list_prod (l : List (Matrix I I K)) {d : ℕ}
    (h : ∀ A ∈ l, OccupiedWord W d A) : OccupiedWord W (l.length*d) l.prod := by
  induction l with
  | nil => simpa using (layerWord_one (K := K) (I := I) 0).occupied (W := W)
  | cons A l ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using (h A List.mem_cons_self).mul
      (ih (fun B hb ↦ h B (List.mem_cons_of_mem _ hb)))

end FiniteFourier
end LinearAlgebra
end OAI
