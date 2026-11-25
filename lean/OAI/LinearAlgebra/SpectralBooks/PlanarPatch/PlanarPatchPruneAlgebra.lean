import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Contractions of one- and two-input tables

These identities implement pruning a labelled tree by summing a constant branch and
absorbing linear maps into a neighbouring vertex. All dimensions may vary independently.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

abbrev LinTable (K : Type*) (q i : ℕ) := Fin q → Fin i → K
abbrev TriTable (K : Type*) (q i j : ℕ) := Fin q → Fin i → Fin j → K

variable {K : Type*} [CommSemiring K] {q i j k l p : ℕ}

def linEval (M : LinTable K q i) (v : Fin i → K) (o : Fin q) : K :=
  ∑ a, M o a * v a

def triEval (B : TriTable K q i j) (v : Fin i → K) (w : Fin j → K) (o : Fin q) : K :=
  ∑ a, ∑ b, B o a b * v a * w b

def linComp (M : LinTable K q i) (N : LinTable K i j) : LinTable K q j :=
  fun o a ↦ ∑ c, M o c * N c a

def linId (q : ℕ) : LinTable K q q :=
  fun o a ↦ if a = o then 1 else 0

def triLeftScalar (B : TriTable K q i j) (v : Fin i → K) : LinTable K q j :=
  fun o b ↦ ∑ a, B o a b * v a

def triRightScalar (B : TriTable K q i j) (w : Fin j → K) : LinTable K q i :=
  fun o a ↦ ∑ b, B o a b * w b

def triPrecomp (B : TriTable K q i j) (M : LinTable K i k) (N : LinTable K j l) :
    TriTable K q k l :=
  fun o a b ↦ ∑ c, ∑ d, B o c d * M c a * N d b

def triPostcomp (M : LinTable K p q) (B : TriTable K q i j) : TriTable K p i j :=
  fun o a b ↦ ∑ t, M o t * B t a b

theorem linEval_comp (M : LinTable K q i) (N : LinTable K i j) (v : Fin j → K) :
    linEval (linComp M N) v = linEval M (linEval N v) := by
  funext o
  simp only [linEval, linComp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

@[simp] theorem linEval_id (v : Fin q → K) : linEval (linId q) v = v := by
  funext o
  simp [linEval, linId, ite_mul]

theorem triEval_leftScalar (B : TriTable K q i j) (v : Fin i → K) (w : Fin j → K) :
    linEval (triLeftScalar B v) w = triEval B v w := by
  funext o
  simp only [linEval, triLeftScalar, triEval, Finset.sum_mul]
  exact Finset.sum_comm

theorem triEval_rightScalar (B : TriTable K q i j) (v : Fin i → K) (w : Fin j → K) :
    linEval (triRightScalar B w) v = triEval B v w := by
  funext o
  simp only [linEval, triRightScalar, triEval, Finset.sum_mul, mul_right_comm]

theorem triEval_precomp (B : TriTable K q i j) (M : LinTable K i k) (N : LinTable K j l)
    (v : Fin k → K) (w : Fin l → K) :
    triEval (triPrecomp B M N) v w = triEval B (linEval M v) (linEval N w) := by
  funext o
  simp only [triEval, triPrecomp, linEval, Finset.sum_mul, Finset.mul_sum]
  let coeff (ab : Fin k × Fin l) (cd : Fin i × Fin j) :=
    B o cd.1 cd.2 * M cd.1 ab.1 * N cd.2 ab.2 * v ab.1 * w ab.2
  calc
    _ = ∑ ab, ∑ cd, coeff ab cd := by simp only [Fintype.sum_prod_type, coeff]
    _ = ∑ cd, ∑ ab, coeff ab cd := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, coeff]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      simp only [mul_comm, mul_left_comm]

theorem triEval_postcomp (M : LinTable K p q) (B : TriTable K q i j)
    (v : Fin i → K) (w : Fin j → K) :
    triEval (triPostcomp M B) v w = linEval M (triEval B v w) := by
  funext o
  simp only [triEval, triPostcomp, linEval, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  let coeff (ab : Fin i × Fin j) (t : Fin q) := M o t * (B t ab.1 ab.2 * (v ab.1 * w ab.2))
  calc
    _ = ∑ ab, ∑ t, coeff ab t := by simp only [Fintype.sum_prod_type, coeff]
    _ = ∑ t, ∑ ab, coeff ab t := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type, coeff]

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
