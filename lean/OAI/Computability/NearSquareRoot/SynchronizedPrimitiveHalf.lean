import OAI.Computability.NearSquareRoot.SynchronizedDilation
import OAI.Computability.NearSquareRoot.SynchronizedWord

/-! # Lifting aligned pair layers to the first half of a borrowed block

A primitive on the first half preserves its kind. For a pair layer the second
half receives a full set of idle pairs, so it can execute the same unconditional
Walsh rounds on the common address bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair

variable {A I : Type*} [DecidableEq A] [DecidableEq I]

/-- Duplicate an existing pairing, with the half tag attached to its spectator index. -/
def halfPairAddress (e : (Fin 2 × I) ≃ A) : Fin 2 × (I ⊕ I) ≃ A ⊕ A :=
  (Equiv.prodSumDistrib (Fin 2) I I).trans (Equiv.sumCongr e e)

/-- Duplicate the pairing layout in the idle half, with identity pairs there. -/
theorem firstHalf_paired (e : (Fin 2 × I) ≃ A) (f : I → PairMatrix) :
    firstHalf ((blockDiagonal f).submatrix e.symm e.symm) =
      (blockDiagonal (Sum.elim f (fun _ : I => 1))).submatrix
        (halfPairAddress e).symm (halfPairAddress e).symm := by
  ext x y
  rcases x with x | x <;> rcases y with y | y
  all_goals
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective y
    simp [firstHalf, fromBlocks, halfPairAddress, blockDiagonal_apply, one_apply, ← ite_and,
      and_comm]

omit [DecidableEq I] in
theorem firstHalf_phase (d : A → ℂ) :
    firstHalf (diagonal d) = diagonal (Sum.elim d fun _ : A => 1) := by
  ext x y
  cases x <;> cases y <;> simp [firstHalf, diagonal_apply, one_apply]

omit [DecidableEq I] in
theorem firstHalf_permutation (e : Equiv.Perm A) :
    firstHalf (fun i j => if i = e j then 1 else 0) =
      (fun i j => if i = e.sumCongr (Equiv.refl A) j then 1 else 0) := by
  ext x y
  cases x <;> cases y <;> simp [firstHalf, fromBlocks, one_apply]

variable [Fintype A]

/-- The first-half embedding preserves matrix products. -/
theorem firstHalf_mul (M N : Matrix A A ℂ) :
    firstHalf (M * N) = firstHalf M * firstHalf N := by
  simp [firstHalf, fromBlocks_multiply]

theorem firstHalf_prod (w : List (Matrix A A ℂ)) :
    (w.map firstHalf).prod = firstHalf w.prod := by
  induction w with
  | nil => simp [firstHalf, fromBlocks_one]
  | cons M w ih => simp [ih, firstHalf_mul]

variable {T : Type} [DecidableEq T]

/-- A permutation, phase diagonal, or pair matching on the occupied half is
a layer of the same kind on the entire ambient space. -/
theorem ShortLayer.firstHalf {M : Matrix T T ℂ} (h : ShortLayer M) :
    ShortLayer (ShortFourier.firstHalf M) := by
  cases h with
  | permutation e =>
    rw [firstHalf_permutation]
    apply ShortLayer.permutation
  | phase d hd =>
    rw [firstHalf_phase]
    exact .phase _ fun i => by cases i <;> simp [hd]
  | pairs e f hf hfa =>
    rw [firstHalf_paired]
    apply ShortLayer.pairs
    · intro k
      cases k with
      | inl i => exact hf i
      | inr i => exact identity_threeWalsh
    · intro k
      cases k with
      | inl i => exact hfa i
      | inr i => simpa using identity_threeWalsh

/-- Running a local word in the occupied half preserves its full primitive layer budget. -/
theorem HasShortWord.firstHalf [Fintype T] {M : Matrix T T ℂ} {n : ℕ} (h : HasShortWord M n) :
    HasShortWord (ShortFourier.firstHalf M) n := by
  obtain ⟨w, rfl, hp, hn⟩ := h
  refine ⟨w.map ShortFourier.firstHalf, firstHalf_prod w, ?_, by simpa using hn⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (hp y hy).firstHalf

end ShortFourier

end NearSquareRoot
end Computability
end OAI
