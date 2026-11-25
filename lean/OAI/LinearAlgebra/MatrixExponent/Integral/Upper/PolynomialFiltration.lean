import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialTensor
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialDegeneration
import Lean.Elab.Tactic.Omega

open OAI.LinearAlgebra.MatrixExponent.Integral

/-!
# The explicit determinant filtration

We use positive dimensions `a+1` and `b+2`.  The two old copies are the
coefficients of `s` and `w`.  The new coordinates are quotient lifts `Q` and
kernel elements `K = W_j - S_(j+1)`.  The first input is unchanged throughout.
All statements below are coefficient identities over the coefficient field.
-/

noncomputable section
open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

private def delta {ι : Type*} [DecidableEq ι] (i j : ι) : O :=
  if j = i then 1 else 0

/-- Two copies of convolution with their first input genuinely shared. -/
def doubledPolynomialTensor (a b : ℕ) :
    Tensor O (Fin (a + 1)) (Fin (b + 2) ⊕ Fin (b + 2))
      (Fin (a + b + 2) ⊕ Fin (a + b + 2))
  | i, Sum.inl j, Sum.inl k => if i.val + j.val = k.val then 1 else 0
  | _, Sum.inl _, Sum.inr _ => 0
  | _, Sum.inr _, Sum.inl _ => 0
  | i, Sum.inr j, Sum.inr k => if i.val + j.val = k.val then 1 else 0

/-- The two-dimensional dot pairing with a singleton first leg. -/
def binaryDotTensor : Tensor O Unit Bool Bool :=
  fun _ y z => if y = z then 1 else 0

def doubleIndexEquiv (n : ℕ) : (Fin n ⊕ Fin n) ≃ (Fin n × Bool) where
  toFun
    | Sum.inl j => (j, false)
    | Sum.inr j => (j, true)
  invFun
    | (j, false) => Sum.inl j
    | (j, true) => Sum.inr j
  left_inv := by intro j; cases j <;> rfl
  right_inv := by rintro ⟨j, b⟩; cases b <;> rfl

def doubleOutputEquiv (a b : ℕ) :
    (Fin (a + b + 2) ⊕ Fin (a + b + 2)) ≃
      (Fin (a + 1 + (b + 2) - 1) × Bool) :=
  (doubleIndexEquiv (a + b + 2)).trans
    (Equiv.prodCongr (finCongr (by omega)) (Equiv.refl Bool))

/-- The doubled coefficient tensor really is convolution tensored with the
two-dimensional dot pairing, after only coordinate equivalences. -/
theorem doubledPolynomialTensor_product (a b : ℕ) :
    Tensor.pullback (fun i => (i, ())) (doubleIndexEquiv (b + 2))
      (doubleOutputEquiv a b)
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) =
      doubledPolynomialTensor a b := by
  funext i y z
  cases y <;> cases z <;>
    simp [Tensor.pullback, Tensor.product, polynomialTensor, binaryDotTensor,
      doubleIndexEquiv, doubleOutputEquiv, doubledPolynomialTensor]

/-- The quotient lifts are `S_0,...,S_(b+1),W_(b+1)`; the remaining
new vectors are `W_j-S_(j+1)` for `j=0,...,b`. -/
def determinantInputMap (b : ℕ) :
    (Fin (b + 3) ⊕ Fin (b + 1)) →
      (Fin (b + 2) ⊕ Fin (b + 2)) → O
  | Sum.inl j, v =>
      if h : j.val < b + 2 then
        delta (Sum.inl ⟨j.val, h⟩) v
      else delta (Sum.inr ⟨b + 1, by omega⟩) v
  | Sum.inr j, v =>
      delta (Sum.inr ⟨j.val, by omega⟩) v -
        delta (Sum.inl ⟨j.val + 1, by omega⟩) v

/-- Coordinates of old output basis vectors in the new basis.  These are the
dual local substitutions required on the tensor's third leg. -/
def determinantOutputMap (a b : ℕ) :
    (Fin (a + b + 3) ⊕ Fin (a + b + 1)) →
      (Fin (a + b + 2) ⊕ Fin (a + b + 2)) → O
  | Sum.inl k, Sum.inl j => if j.val = k.val then 1 else 0
  | Sum.inl k, Sum.inr j => if j.val + 1 = k.val then 1 else 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr k, Sum.inr j => if j.val = k.val then 1 else 0

/-- The whole transformed tensor, including the cross block. -/
def determinantAdaptedTensor (a b : ℕ) :
    Tensor O (Fin (a + 1)) (Fin (b + 3) ⊕ Fin (b + 1))
      (Fin (a + b + 3) ⊕ Fin (a + b + 1))
  | i, Sum.inl j, Sum.inl k => if i.val + j.val = k.val then 1 else 0
  | i, Sum.inl j, Sum.inr k =>
      if j.val = b + 2 ∧ i.val + b + 1 = k.val then 1 else 0
  | _, Sum.inr _, Sum.inl _ => 0
  | i, Sum.inr j, Sum.inr k => if i.val + j.val = k.val then 1 else 0

private theorem doubled_left (a b : ℕ) (i : Fin (a + 1)) (j : Fin (b + 2)) :
    doubledPolynomialTensor a b i (Sum.inl j) =
      delta (Sum.inl (⟨i.val + j.val, by omega⟩ : Fin (a + b + 2))) := by
  funext z
  cases z with
  | inl k => simp [doubledPolynomialTensor, delta, Fin.ext_iff, eq_comm]
  | inr k => simp [doubledPolynomialTensor, delta]

private theorem doubled_right (a b : ℕ) (i : Fin (a + 1)) (j : Fin (b + 2)) :
    doubledPolynomialTensor a b i (Sum.inr j) =
      delta (Sum.inr (⟨i.val + j.val, by omega⟩ : Fin (a + b + 2))) := by
  funext z
  cases z with
  | inl k => simp [doubledPolynomialTensor, delta]
  | inr k => simp [doubledPolynomialTensor, delta, Fin.ext_iff, eq_comm]

private theorem restrict_single_second {X Y Z Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor O X Y Z) (B : Y' → Y → O) (C : Z' → Z → O)
    (x : X) (y : Y') (z : Z') (v : Y)
    (hB : B y = delta v) :
    Tensor.restrict delta B C T x y z = ∑ w, C z w * T x v w := by
  simp [Tensor.restrict, hB, delta, ite_mul, mul_ite]

private theorem restrict_difference_second {X Y Z Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor O X Y Z) (B : Y' → Y → O) (C : Z' → Z → O)
    (x : X) (y : Y') (z : Z') (v w : Y)
    (hB : B y = fun u => delta v u - delta w u) :
    Tensor.restrict delta B C T x y z =
      (∑ u, C z u * T x v u) - ∑ u, C z u * T x w u := by
  simp [Tensor.restrict, hB, delta, ite_mul,
    sub_mul, Finset.sum_sub_distrib]

/-- The simultaneous basis change is an actual three-leg restriction.  In
particular no branch-specific first-input substitution is used. -/
theorem determinant_basis_change (a b : ℕ) :
    Tensor.restrict delta (determinantInputMap b) (determinantOutputMap a b)
      (doubledPolynomialTensor a b) = determinantAdaptedTensor a b := by
  funext i y z
  cases y with
  | inl j =>
      by_cases hj : j.val < b + 2
      · rw [restrict_single_second (doubledPolynomialTensor a b)
          (determinantInputMap b) (determinantOutputMap a b) i (Sum.inl j) z
          (Sum.inl ⟨j.val, hj⟩) (by funext v; simp [determinantInputMap, hj])]
        rw [doubled_left]
        simp only [delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        cases z with
        | inl k => rfl
        | inr k => simp [determinantOutputMap, determinantAdaptedTensor,
            show j.val ≠ b + 2 by omega]
      · have hlast : j.val = b + 2 := by omega
        rw [restrict_single_second (doubledPolynomialTensor a b)
          (determinantInputMap b) (determinantOutputMap a b) i (Sum.inl j) z
          (Sum.inr ⟨b + 1, by omega⟩) (by funext v; simp [determinantInputMap, hj])]
        rw [doubled_right]
        simp only [delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        cases z with
        | inl k =>
            simp [determinantOutputMap, determinantAdaptedTensor, hlast,
              Nat.add_assoc]
        | inr k => simp [determinantOutputMap, determinantAdaptedTensor, hlast,
            Nat.add_assoc]
  | inr j =>
      rw [restrict_difference_second _ _ _ i (Sum.inr j) z
        (Sum.inr ⟨j.val, by omega⟩) (Sum.inl ⟨j.val + 1, by omega⟩) rfl]
      rw [doubled_right, doubled_left]
      simp only [delta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      cases z with
      | inl k => simp [determinantOutputMap, determinantAdaptedTensor, Nat.add_assoc]
      | inr k => simp [determinantOutputMap, determinantAdaptedTensor]

/-- The two retained diagonal branches, still sharing the same first leg. -/
def determinantGradedTensor (a b : ℕ) :
    Tensor O (Fin (a + 1)) (Fin (b + 3) ⊕ Fin (b + 1))
      (Fin (a + b + 3) ⊕ Fin (a + b + 1))
  | i, Sum.inl j, Sum.inl k => if i.val + j.val = k.val then 1 else 0
  | _, Sum.inl _, Sum.inr _ => 0
  | _, Sum.inr _, Sum.inl _ => 0
  | i, Sum.inr j, Sum.inr k => if i.val + j.val = k.val then 1 else 0

theorem determinantGraded_quotient (a b : ℕ) (i : Fin (a + 1))
    (j : Fin (b + 3)) (k : Fin (a + 1 + (b + 3) - 1)) :
    determinantGradedTensor a b i (Sum.inl j)
      (Sum.inl (Fin.cast (by omega) k)) =
      polynomialTensor (a + 1) (b + 3) i j k := by
  rfl

theorem determinantGraded_kernel (a b : ℕ) (i : Fin (a + 1))
    (j : Fin (b + 1)) (k : Fin (a + 1 + (b + 1) - 1)) :
    determinantGradedTensor a b i (Sum.inr j)
      (Sum.inr (Fin.cast (by omega) k)) =
      polynomialTensor (a + 1) (b + 1) i j k := by
  rfl

@[simp] theorem determinantGraded_quotient_kernel (a b : ℕ) (i : Fin (a + 1))
    (j : Fin (b + 3)) (k : Fin (a + b + 1)) :
    determinantGradedTensor a b i (Sum.inl j) (Sum.inr k) = 0 := rfl

@[simp] theorem determinantGraded_kernel_quotient (a b : ℕ) (i : Fin (a + 1))
    (j : Fin (b + 1)) (k : Fin (a + b + 3)) :
    determinantGradedTensor a b i (Sum.inr j) (Sum.inl k) = 0 := rfl

def determinantInputWeight (b : ℕ) : (Fin (b + 3) ⊕ Fin (b + 1)) → ℤ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

def determinantOutputWeight (a b : ℕ) :
    (Fin (a + b + 3) ⊕ Fin (a + b + 1)) → ℤ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem determinant_supported_weight (a b : ℕ)
    (i : Fin (a + 1)) (y : Fin (b + 3) ⊕ Fin (b + 1))
    (z : Fin (a + b + 3) ⊕ Fin (a + b + 1))
    (h : determinantAdaptedTensor a b i y z ≠ 0) :
    0 ≤ (0 : ℤ) + determinantInputWeight b y + determinantOutputWeight a b z := by
  cases y <;> cases z <;>
    simp_all [determinantAdaptedTensor, determinantInputWeight, determinantOutputWeight]

theorem determinant_weightedLimit (a b : ℕ) :
    weightedLimit (determinantAdaptedTensor a b) (fun _ => 0)
      (determinantInputWeight b) (determinantOutputWeight a b) =
      determinantGradedTensor a b := by
  funext i y z
  cases y <;> cases z <;>
    simp [weightedLimit, determinantAdaptedTensor, determinantGradedTensor,
      determinantInputWeight, determinantOutputWeight]

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
