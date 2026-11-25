import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Star batches for rational coordinate changes

In Gaussian pivot elimination an entire row-clearing or column-clearing batch
has a common source or a common target. It therefore needs only one move of
the center to an extreme physical position and one move back. The number
of such batches grows linearly with the number of address fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix Matrix.TransvectionStruct Sum

/-- Every elementary addition in a batch uses the same destination or the
same source coordinate. -/
def IsStar {I : Type*} (s : List (TransvectionStruct I ℚ)) : Prop :=
  (∃ i, ∀ a ∈ s, a.i = i) ∨ (∃ j, ∀ a ∈ s, a.j = j)

theorem isStar_singleton {I : Type*} (t : TransvectionStruct I ℚ) :
    IsStar [t] := Or.inl ⟨t.i, by simp⟩

private theorem pivot_nonzero_stars {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) ℚ)
    (hM : M (inr ()) (inr ()) ≠ 0) :
    ∃ L R : List (TransvectionStruct (Fin r ⊕ Unit) ℚ),
      IsStar L ∧ IsStar R ∧
      IsTwoBlockDiagonal ((L.map toMatrix).prod * M * (R.map toMatrix).prod) := by
  let L : List (TransvectionStruct (Fin r ⊕ Unit) ℚ) :=
    List.ofFn fun i : Fin r =>
      ⟨inl i, inr (), by simp, -M (inl i) (inr ()) / M (inr ()) (inr ())⟩
  let R : List (TransvectionStruct (Fin r ⊕ Unit) ℚ) :=
    List.ofFn fun i : Fin r =>
      ⟨inr (), inl i, by simp, -M (inr ()) (inl i) / M (inr ()) (inr ())⟩
  refine ⟨L, R, Or.inr ⟨inr (), ?_⟩, Or.inl ⟨inr (), ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rfl
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rfl
  · have hL : L.map toMatrix = Pivot.listTransvecCol M := by
      simp [L, Pivot.listTransvecCol, Function.comp_def]
    have hR : R.map toMatrix = Pivot.listTransvecRow M := by
      simp [R, Pivot.listTransvecRow, Function.comp_def]
    rw [hL, hR]
    exact Pivot.isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow M hM

/-- One Gaussian elimination step has at most three common-center batches,
including the initial pivot repair when the bottom-right entry is zero. -/
theorem pivot_stars {r : ℕ} (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) ℚ) :
    ∃ L R : List (List (TransvectionStruct (Fin r ⊕ Unit) ℚ)),
      (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧ L.length + R.length ≤ 3 ∧
      IsTwoBlockDiagonal ((L.flatten.map toMatrix).prod * M * (R.flatten.map toMatrix).prod) := by
  by_cases hd : IsTwoBlockDiagonal M
  · exact ⟨[], [], by simp, by simp, by simp, by simpa using hd⟩
  by_cases hz : M (inr ()) (inr ()) = 0
  · have h : ∃ i : Fin r, M (inl i) (inr ()) ≠ 0 ∨ M (inr ()) (inl i) ≠ 0 := by
      contrapose! hd
      constructor
      · ext i u
        cases u
        exact (hd i).1
      · ext u i
        cases u
        exact (hd i).2
    obtain ⟨i, h | h⟩ := h
    · let t : TransvectionStruct (Fin r ⊕ Unit) ℚ := ⟨inr (), inl i, by simp, 1⟩
      have hp : (t.toMatrix * M) (inr ()) (inr ()) ≠ 0 := by
        simpa [t, hz] using h
      obtain ⟨l, r, hl, hr, hblock⟩ := pivot_nonzero_stars _ hp
      refine ⟨[l, [t]], [r], by simp [hl, isStar_singleton], by simpa, by simp, ?_⟩
      simpa [Matrix.mul_assoc] using hblock
    · let t : TransvectionStruct (Fin r ⊕ Unit) ℚ := ⟨inl i, inr (), by simp, 1⟩
      have hp : (M * t.toMatrix) (inr ()) (inr ()) ≠ 0 := by
        simpa [t, hz] using h
      obtain ⟨l, r, hl, hr, hblock⟩ := pivot_nonzero_stars _ hp
      refine ⟨[l], [[t],r], by simpa, by simp [hr, isStar_singleton], by simp, ?_⟩
      simpa [Matrix.mul_assoc] using hblock
  · obtain ⟨l, r, hl, hr, hblock⟩ := pivot_nonzero_stars M hz
    exact ⟨[l], [r], by simpa, by simpa, by simp, by simpa using hblock⟩

end Interchange

end NearSquareRoot
end Computability
end OAI
