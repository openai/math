import OAI.LinearAlgebra.MatrixExponent.Coefficients
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialApproximation
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
import Mathlib.Tactic.Choose

open OAI.LinearAlgebra.MatrixExponent

/-!
# Polynomial coefficient extraction by actual restrictions

Every coefficient of a bounded polynomial tensor is a linear combination of
evaluations at common interpolation nodes. If those evaluations are local
restrictions of one source tensor, the coefficient is a restriction of the
full direct sum of that many source copies. Applying this to tensor powers
gives the linear interpolation overhead required by restriction-monotone
characters. No continuity of a character on a Euclidean closure is assumed.
-/

noncomputable section

open scoped BigOperators
open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Upper.Separation

section RestrictionAlgebra

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Independent maps on each full source copy may have the same target. The
result is the sum of their restricted tensors, with no cross-copy terms. -/
theorem restrict_directSum_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → Tensor Coeff X Y Z)
    (a : ι → U → X → Coeff) (b : ι → V → Y → Coeff) (c : ι → W → Z → Coeff) :
    Tensor.restrict (fun u x => a x.1 u x.2)
      (fun v y => b y.1 v y.2) (fun w z => c z.1 w z.2)
      (Tensor.directSum T) =
      fun u v w => ∑ i, Tensor.restrict (a i) (b i) (c i) (T i) u v w := by
  classical
  funext u v w
  simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
    ite_and, mul_ite]

/-- Scaling one local map scales the whole restricted coefficient tensor. -/
theorem restrict_scale_first (T : Tensor Coeff X Y Z)
    (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff) (s : Coeff) :
    Tensor.restrict (fun u x => s * a u x) b c T =
      fun u v w => s * Tensor.restrict a b c T u v w := by
  funext u v w
  simp only [Tensor.restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Tensor products of the local maps give a local restriction of every power.
Every input coordinate in every position is summed independently. -/
theorem restrict_power (T : Tensor Coeff X Y Z)
    (a : U → X → Coeff) (b : V → Y → Coeff) (c : W → Z → Coeff) (j : ℕ) :
    Tensor.restrict
      (fun u x => ∏ i, a (u i) (x i))
      (fun v y => ∏ i, b (v i) (y i))
      (fun w z => ∏ i, c (w i) (z i)) (Tensor.power T j) =
      Tensor.power (Tensor.restrict a b c T) j := by
  funext u v w
  simp only [Tensor.restrict, Tensor.power, Fintype.prod_sum,
    Finset.prod_mul_distrib]

theorem power_mem_restrictionOrbit {T : Tensor Coeff X Y Z}
    {S : Tensor Coeff U V W} (h : S ∈ LocalTensor.orbit T) (j : ℕ) :
    Tensor.power S j ∈ LocalTensor.orbit (Tensor.power T j) := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨(fun u x => ∏ i, a (u i) (x i)),
    (fun v y => ∏ i, b (v i) (y i)),
    (fun w z => ∏ i, c (w i) (z i)), (restrict_power T a b c j).symm⟩

end RestrictionAlgebra

section Interpolation

variable {X Y Z U V W : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]

/-- Interpolation at any common family of distinct nonzero nodes turns actual
restriction witnesses for the evaluations into one restriction witness for the
coefficient. The full number of source copies is charged explicitly. -/
theorem polynomial_coeff_mem_restrictionOrbit {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (T : Tensor Coeff X Y Z) (P : Tensor (Polynomial Coeff) U V W)
    (nodes : ι → Coeff) (hinj : Function.Injective nodes)
    (hnonzero : ∀ i, nodes i ≠ 0)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (hdegree : ∀ u v w, (P u v w).degree < Fintype.card ι) (d : ℕ) :
    (fun u v w => (P u v w).coeff d) ∈
      LocalTensor.orbit (Tensor.directSum (fun _ : ι => T)) := by
  classical
  have hex : ∀ i : ι, ∃ (a : U → X → Coeff) (b : V → Y → Coeff)
      (c : W → Z → Coeff),
      (fun u v w => (P u v w).eval (nodes i)) = Tensor.restrict a b c T := by
    intro i
    exact heval (nodes i) (hnonzero i)
  choose a b c hrestriction using hex
  let weight : ι → Coeff := fun i => (Lagrange.basis Finset.univ nodes i).coeff d
  refine ⟨(fun u x => weight x.1 * a x.1 u x.2),
    (fun v y => b y.1 v y.2), (fun w z => c z.1 w z.2), ?_⟩
  rw [restrict_directSum_sum (fun _ : ι => T) (fun i u x => weight i * a i u x) b c]
  funext u v w
  rw [Tensor.coeff_eq_sum_eval nodes hinj _ d (hdegree u v w)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [restrict_scale_first]
  have h := congrFun (congrFun (congrFun (hrestriction i) u) v) w
  dsimp [weight]
  rw [h]
  ring

theorem polynomial_power_constant (P : Tensor (Polynomial Coeff) U V W) (j : ℕ) :
    (fun u v w => (Tensor.power P j u v w).coeff 0) =
      Tensor.power (fun u v w => (P u v w).coeff 0) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.coeff_zero_prod]

theorem polynomial_power_eval (P : Tensor (Polynomial Coeff) U V W) (j : ℕ) (t : Coeff) :
    (fun u v w => (Tensor.power P j u v w).eval t) =
      Tensor.power (fun u v w => (P u v w).eval t) j := by
  funext u v w
  simp only [Tensor.power, Polynomial.eval_prod]

theorem polynomial_power_degree (P : Tensor (Polynomial Coeff) U V W) (K j : ℕ)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (u : Fin j → U) (v : Fin j → V) (w : Fin j → W) :
    (Tensor.power P j u v w).degree ≤ K * j := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (Tensor.power P j u v w).natDegree ≤
        ∑ i, (P (u i) (v i) (w i)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin j, K := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_le_of_degree_le (hdegree (u i) (v i) (w i))
    _ = K * j := by simp [Nat.mul_comm]

/-- The finite interpolation bound before applying any character. For every
power `j`, exactly `K*j+1` copies of the power of the original source suffice.
The infinite field supplies distinct nonzero nodes. -/
theorem polynomial_power_mem_restrictionOrbit
    (T : Tensor Coeff X Y Z) (D : Tensor Coeff U V W)
    (P : Tensor (Polynomial Coeff) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T)
    (j : ℕ) :
    Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j)) := by
  classical
  obtain ⟨nodes, hinj, hnonzero⟩ := exists_nonzero_nodes (F := Coeff) (K * j + 1)
  have hevalpower : ∀ t : Coeff, t ≠ 0 →
      (fun u v w => (Tensor.power P j u v w).eval t) ∈
        LocalTensor.orbit (Tensor.power T j) := by
    intro t ht
    rw [polynomial_power_eval]
    exact power_mem_restrictionOrbit (heval t ht) j
  have hdegreepower : ∀ u v w, (Tensor.power P j u v w).degree <
      Fintype.card (Fin (K * j + 1)) := by
    intro u v w
    simp only [Fintype.card_fin]
    exact lt_of_le_of_lt (polynomial_power_degree P K j hdegree u v w)
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self (K * j)))
  have h := polynomial_coeff_mem_restrictionOrbit (Tensor.power T j) (Tensor.power P j)
    nodes hinj hnonzero hevalpower hdegreepower 0
  have hD : (fun u v w => (P u v w).coeff 0) = D := by
    funext u v w
    exact hconstant u v w
  rw [polynomial_power_constant, hD] at h
  exact h

end Interpolation

end OAI.LinearAlgebra.MatrixExponent.Upper.Separation
