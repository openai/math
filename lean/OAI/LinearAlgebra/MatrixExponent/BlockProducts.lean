import OAI.LinearAlgebra.MatrixExponent.Integral.Model
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Applying a scalar rank decomposition to blocks

The coefficients belong to the base ring. The input entries may live in an
algebra, in particular the polynomial ring of a smaller padded input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] {i j k r d e f : ℕ}

def joinPos (z : Pos i j) (p : Pos d e) : Pos (i * d) (j * e) :=
  (finProdFinEquiv (z.1, p.1), finProdFinEquiv (z.2, p.2))

def mm (X : Pos i k → K) (Y : Pos k j → K) (p : Pos i j) : K :=
  ∑ l, X (p.1, l) * Y (l, p.2)

def linBlock (a : Pos i j → F) (X : Pos (i * d) (j * e) → K) (p : Pos d e) : K :=
  ∑ z, algebraMap F K (a z) * X (joinPos z p)

private theorem eval_formula (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F)
    (c : Fin r → Pos i j → F) (h : ∀ x y z, ∑ l, a l x * b l y * c l z =
      if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then 1 else 0)
    (v : Pos i k → K) (w : Pos k j → K) (z : Pos i j) :
    ∑ l, algebraMap F K (c l z) *
      ((∑ x, algebraMap F K (a l x) * v x) * (∑ y, algebraMap F K (b l y) * w y)) =
      mm v w z := by
  classical
  calc
    _ = ∑ l, ∑ x, ∑ y, algebraMap F K (a l x * b l y * c l z) * v x * w y := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum, map_mul, mul_comm, mul_left_comm]
    _ = ∑ x, ∑ y, algebraMap F K (∑ l, a l x * b l y * c l z) * v x * w y := by
      simp only [map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = mm v w z := by
      simp [h, apply_ite, ite_mul, ite_and, Fintype.sum_prod_type, Finset.sum_ite_irrel, mm]

theorem block_formula (h : Integral.Rank F i j k r) :
    ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
      ∀ (X : Pos (i * d) (k * f) → K) (Y : Pos (k * f) (j * e) → K)
        (z : Pos i j) (p : Pos d e),
      mm X Y (joinPos z p) =
        ∑ l, algebraMap F K (c l z) * mm (linBlock (a l) X) (linBlock (b l) Y) p := by
  obtain ⟨a, b, c, habc⟩ := h
  refine ⟨a, b, c, ?_⟩
  intro X Y z p
  simp only [mm, Finset.mul_sum]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact (eval_formula a b c habc (fun x => X (joinPos x (p.1, l)))
    (fun y => Y (joinPos y (l, p.2))) z).symm

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI.LinearAlgebra.MatrixExponent

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {n r d : ℕ}

abbrev joinPos (z : Pos n) (p : Pos d) : Pos (n * d) := Rectangle.joinPos z p

abbrev mm (X Y : Pos n → K) (p : Pos n) : K := Rectangle.mm X Y p

abbrev linBlock (a : Pos n → F) (X : Pos (n * d) → K) (p : Pos d) : K :=
  Rectangle.linBlock a X p

theorem block_formula (h : RankLE F n r) :
    ∃ a b c : Fin r → Pos n → F, ∀ (X Y : Pos (n * d) → K) (z : Pos n) (p : Pos d),
      mm X Y (joinPos z p) =
        ∑ i, algebraMap F K (c i z) * mm (linBlock (a i) X) (linBlock (b i) Y) p :=
  Rectangle.block_formula h

end OAI.LinearAlgebra.MatrixExponent
