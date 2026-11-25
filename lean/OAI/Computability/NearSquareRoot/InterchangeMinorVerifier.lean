import OAI.Computability.NearSquareRoot.InterchangeConfiguredBatch

/-! # Checking the proposed rank without computing an abstract module rank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.MinorROM

open Matrix

variable {L K : Type} [Fintype L] [Field K] {h : ℕ}

/-- Finite data for a rank factorization: a row and column selection and a
candidate inverse for the selected minor. -/
structure Code (L K : Type) (h : ℕ) where
  row : Fin h → L
  col : Fin h → L
  middle : Matrix (Fin h) (Fin h) K

def valid [DecidableEq L] [DecidableEq K] (A : Matrix L L K) (c : Code L K h) : Bool :=
  decide ((∀ i j, c.row i = c.row j → i = j) ∧ (∀ i j, c.col i = c.col j → i = j) ∧
    A.submatrix c.row c.col * c.middle = 1 ∧
    A.submatrix id c.col * c.middle * A.submatrix c.row id = A)

theorem valid_iff [DecidableEq L] [DecidableEq K] (A : Matrix L L K) (c : Code L K h) :
    valid A c = true ↔ Function.Injective c.row ∧ Function.Injective c.col ∧
      A.submatrix c.row c.col * c.middle = 1 ∧
      A.submatrix id c.col * c.middle * A.submatrix c.row id = A := by
  rw [valid,decide_eq_true_iff]
  rfl

theorem rank_of_valid [DecidableEq L] [DecidableEq K] (A : Matrix L L K) (c : Code L K h)
    (hc : valid A c = true) : h = A.rank := by
  obtain ⟨_,_,inverse,factor⟩ := (valid_iff _ _).mp hc
  apply Nat.le_antisymm
  · have h' := (rank_mul_le_left (A.submatrix c.row c.col) c.middle).trans
      (A.rank_submatrix_le c.row c.col)
    simpa [inverse] using h'
  · have h' := (rank_mul_le_right (A.submatrix id c.col * c.middle) (A.submatrix c.row id)).trans
      (A.submatrix c.row id).rank_le_card_height
    simpa [factor] using h'

/-- The finite arithmetic test accepts a certificate at the exact abstract rank. -/
theorem complete [DecidableEq L] [DecidableEq K] (A : Matrix L L K) :
    ∃ c : Code L K A.rank, valid A c = true := by
  obtain ⟨I,J,hi,hj,iu,hf⟩ := exists_skeleton A
  refine ⟨⟨I,J,(A.submatrix I J)⁻¹⟩,(valid_iff _ _).mpr ⟨hi,hj,?_,hf⟩⟩
  exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp iu)

/-- A passing minor directly supplies the selected shared rows of the Hamming
stage. All dependence on the abstract rank is in the type cast. -/
def select {p k h : ℕ} [Fact p.Prime]
    (c : Code (HammingLabels p k) (ZMod p) h)
    (hc : valid (hammingLabelMatrix p (2^k)) c = true) :
    Code (HammingLabels p k) (ZMod p) (hammingLabelMatrix p (2^k)).rank :=
  rank_of_valid _ c hc ▸ c

theorem select_factor {p k h : ℕ} [Fact p.Prime]
    (c : Code (HammingLabels p k) (ZMod p) h)
    (hc : valid (hammingLabelMatrix p (2^k)) c = true) :
    let d := select c hc
    Function.Injective d.row ∧ Function.Injective d.col ∧
      (rectangleMatrix (K:=ZMod p) (nodeRectangles p k)).submatrix id d.col * d.middle *
      (rectangleMatrix (nodeRectangles p k)).submatrix d.row id = rectangleMatrix (nodeRectangles p k) := by
  intro d
  obtain rfl := rank_of_valid _ c hc
  obtain ⟨hi,hj,_,hf⟩ := (valid_iff _ _).mp hc
  refine ⟨hi,hj,?_⟩
  unfold nodeRectangles
  rw [rectangleMatrix_hammingRectangle]
  exact hf

end Interchange.MinorROM

end NearSquareRoot
end Computability
end OAI
