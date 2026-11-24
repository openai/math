import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-! Coefficient extraction for opposite-order products of energy-graded matrices.
The grades can be doubled fermionic energies, which are integers for all states. -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open scoped BigOperators
open LaurentPolynomial

variable {R ι : Type*} [CommRing R]

/-- Retain the entries of an operator that change the energy by exactly `q`. -/
def energyMode (energy : ι → ℤ) (A : Matrix ι ι R) (q : ℤ) : Matrix ι ι R :=
  fun i j => if energy i - energy j = q then A i j else 0

/-- Record the energy change of an operator entry as a Laurent monomial. -/
noncomputable def energyField (energy : ι → ℤ) (h : ℤ) (A : Matrix ι ι R) :
    Matrix ι ι (LaurentPolynomial R) :=
  fun i j => C (A i j) * T (energy i - energy j - h)

private lemma monomial_coeff_product (c a b : R) (u v t : ℤ) :
    (C c * T u * ((C a * T v) * C b)).coeff t =
      if u + v = t then c * (a * b) else 0 := by
  have h : C c * T u * ((C a * T v) * C b) = C (c * (a * b)) * T (u + v) := by
    rw [map_mul, map_mul, T_add]
    ring
  rw [h, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

private lemma binomial_laurent (d : ℕ) :
    (T (R := R) 2 - 1) ^ d =
      ∑ a : Fin (d + 1), C ((-1 : R) ^ (a : ℕ) * d.choose a) *
        T ((d - (a : ℕ) : ℕ) * (2 : ℤ)) := by
  classical
  rw [show T (R := R) 2 - 1 = -1 + T 2 by ring, add_pow]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro a _
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, T_pow]
  ring

variable [Fintype ι]

/-- Read an arbitrary coefficient of the forward product, including its binomial multiplier. -/
theorem forward_coeff_any_energy (energy : ι → ℤ) (h t : ℤ) (A B : Matrix ι ι R)
    (d : ℕ) (i j : ι) :
    ((T (R := R) 2 - 1) ^ d * (energyField energy h A * B.map C) i j).coeff t =
      ∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
        (let q := t + h - (d - (a : ℕ) : ℕ) * (2 : ℤ)
         (energyMode energy A q * energyMode energy B (energy i - energy j - q)) i j) := by
  classical
  rw [binomial_laurent, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Matrix.map_apply, energyField]
  apply Finset.sum_congr rfl
  intro k _
  rw [monomial_coeff_product]
  dsimp only [energyMode]
  split_ifs <;> first | (exfalso; omega) | ring

/-- Coefficient between states of the same energy. -/
theorem forward_coeff (energy : ι → ℤ) (h t : ℤ) (A B : Matrix ι ι R)
    (d : ℕ) (i j : ι) (hij : energy i = energy j) :
    ((T (R := R) 2 - 1) ^ d * (energyField energy h A * B.map C) i j).coeff t =
      ∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
        (let q := t + h - (d - (a : ℕ) : ℕ) * (2 : ℤ)
         (energyMode energy A q * energyMode energy B (-q)) i j) := by
  simpa only [hij, sub_self, zero_sub] using forward_coeff_any_energy energy h t A B d i j

/-- Read the same Laurent coefficient with the two operators in reverse order. -/
theorem reverse_coeff_any_energy (energy : ι → ℤ) (h t : ℤ) (A B : Matrix ι ι R)
    (d : ℕ) (i j : ι) :
    ((T (R := R) 2 - 1) ^ d * (B.map C * energyField energy h A) i j).coeff t =
      ∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
        (let q := t + h - (d - (a : ℕ) : ℕ) * (2 : ℤ)
         (energyMode energy B (energy i - energy j - q) * energyMode energy A q) i j) := by
  classical
  rw [binomial_laurent, Finset.sum_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Matrix.map_apply, energyField]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (C (B i k)) (C (A k j) * T _), monomial_coeff_product]
  dsimp only [energyMode]
  split_ifs <;> first | (exfalso; omega) | ring

/-- Coefficient between states of the same energy. -/
theorem reverse_coeff (energy : ι → ℤ) (h t : ℤ) (A B : Matrix ι ι R)
    (d : ℕ) (i j : ι) (hij : energy i = energy j) :
    ((T (R := R) 2 - 1) ^ d * (B.map C * energyField energy h A) i j).coeff t =
      ∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
        (let q := t + h - (d - (a : ℕ) : ℕ) * (2 : ℤ)
         (energyMode energy B (-q) * energyMode energy A q) i j) := by
  simpa only [hij, sub_self, zero_sub] using reverse_coeff_any_energy energy h t A B d i j


/-- The product of two modes vanishes outside its total energy shift. -/
theorem modes_off_energy (energy : ι → ℤ) (A B : Matrix ι ι R)
    (r s : ℤ) (i j : ι) (hij : energy i - energy j ≠ r+s) :
    (energyMode energy A r * energyMode energy B s) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  dsimp only [energyMode]
  split_ifs <;> first | (exfalso; omega) | simp

/-- Opposite energy changes give zero on matrix entries of different energies. -/
theorem opposite_modes_off_energy (energy : ι → ℤ) (A B : Matrix ι ι R)
    (q : ℤ) (i j : ι) (hij : energy i ≠ energy j) :
    (energyMode energy A q * energyMode energy B (-q)) i j = 0 :=
  modes_off_energy energy A B q (-q) i j (by omega)

/-- Bivariate coefficient readout between states whose energy difference agrees
with the total degree of the selected monomial. The two exponents of the fields
are `p-d+a` and `q-a` before multiplication by the binomial. -/
theorem bivariate_supercommutator_readout (energy : ι → ℤ) (A B : Matrix ι ι R)
    (hA hB p q : ℤ) (ε : R) (d : ℕ) (hd : 2 * (d : ℤ) + 2 = hA + hB)
    (i j : ι) (hij : energy i - energy j = 2*(p+q+1)) :
    ((T (R := R) 2 - 1) ^ d * (energyField energy hA A * B.map C) i j).coeff (2*p) -
      ε * ((T (R := R) 2 - 1) ^ d * (B.map C * energyField energy hA A) i j).coeff (2*p) =
      ∑ a : Fin (d+1), (-1 : R)^(a : ℕ) * d.choose a *
        (let r := 2*(p-d+(a:ℕ))+hA
         let s := 2*(q-(a:ℕ))+hB
         (energyMode energy A r * energyMode energy B s) i j -
           ε * (energyMode energy B s * energyMode energy A r) i j) := by
  rw [forward_coeff_any_energy, reverse_coeff_any_energy, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have ha := a.isLt
  have hr : 2*p+hA - (d-(a:ℕ):ℕ)*(2:ℤ) = 2*(p-d+(a:ℕ))+hA := by omega
  have hs : energy i - energy j - (2*(p-d+(a:ℕ))+hA) = 2*(q-(a:ℕ))+hB := by omega
  dsimp only
  rw [hr, hs]
  ring

/-- With doubled energies and the paper's coefficient index `s`, the first order
raises the intermediate energy by `2 * s+hB-2*a` and the second order lowers it
by the same amount. Here `ε` is the sign in the supercommutator. -/
theorem shifted_supercommutator_readout (energy : ι → ℤ) (A B : Matrix ι ι R)
    (hA hB s : ℤ) (ε : R) (d : ℕ) (hd : 2 * (d : ℤ) + 2 = hA + hB)
    (i j : ι) (hij : energy i = energy j) :
    ((T (R := R) 2 - 1) ^ d * (energyField energy hA A * B.map C) i j).coeff (-2 * s - 2) -
      ε * ((T (R := R) 2 - 1) ^ d * (B.map C * energyField energy hA A) i j).coeff (-2 * s - 2) =
      ∑ a : Fin (d + 1), (-1 : R) ^ (a : ℕ) * d.choose a *
        (let q := 2 * s + hB - 2 * (a : ℕ)
         (energyMode energy A (-q) * energyMode energy B q) i j -
           ε * (energyMode energy B q * energyMode energy A (-q)) i j) := by
  rw [forward_coeff energy hA _ A B d i j hij, reverse_coeff energy hA _ A B d i j hij,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have ha := a.isLt
  have hq : -2 * s - 2 + hA - (d - (a : ℕ) : ℕ) * (2 : ℤ) =
      -(2 * s + hB - 2 * (a : ℕ)) := by omega
  simp only [hq, neg_neg]
  ring

end Crossing

end VPVNP
end Computability
end OAI
