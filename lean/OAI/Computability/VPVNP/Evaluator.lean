import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Counting a monomial in a finite algebra

The evaluator of Section 8.2 processes base-`Q` digits most significant first
using the linear maps for Frobenius and multiplication by a label. Once a
basis of the coefficient algebra containing `1` is given, an index path
through their matrices contributes a product of entries in the slice field.
The final prime-field coordinate of this product determines the number of
accepting branches.

`finiteAlgebra_pathCount` proves equation (8.2) for these branches, and
`digitProgram_length_le` bounds the number of linear steps. The construction
of a slice and the algorithms for querying individual matrix entries are
separate parts of Theorem 8.1 and Appendix D.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator

section Digits

variable (K : Type*) [Field K] [Fintype K]
variable {A : Type*} [CommRing A] [Algebra K A] {t : ℕ}

/-- The linear steps for one digit position. The `i`th digit is `d i`. -/
def digitSteps (X : Fin t → A) (d : Fin t → ℕ) : List (A →ₗ[K] A) :=
  (FiniteField.frobeniusAlgHom K A).toLinearMap ::
    (List.finRange t).flatMap (fun i => List.replicate (d i) (LinearMap.mulLeft K (X i)))

/-- The linear program for the low `width` base-`#K` digits of every exponent.
The recursive call on the quotients processes the more significant digits first. -/
def digitProgram (X : Fin t → A) : ℕ → (Fin t → ℕ) → List (A →ₗ[K] A)
  | 0, _ => []
  | width + 1, e =>
    digitProgram X width (fun i => e i / Fintype.card K) ++
      digitSteps K X (fun i => e i % Fintype.card K)

omit [Fintype K] in
private lemma apply_repeated_label (x v : A) (d : ℕ) :
    (List.replicate d (LinearMap.mulLeft K x)).foldl (fun a M => M a) v = v * x ^ d := by
  induction d generalizing v with
  | zero => simp
  | succ d ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, pow_succ]
    change x * v * x ^ d = v * (x ^ d * x)
    ac_rfl

omit [Fintype K] in
private lemma apply_label_digits (X : Fin t → A) (d : Fin t → ℕ) (s : List (Fin t)) (v : A) :
    (s.flatMap fun i => List.replicate (d i) (LinearMap.mulLeft K (X i))).foldl
      (fun a M => M a) v = v * (s.map fun i => X i ^ d i).prod := by
  induction s generalizing v with
  | nil => simp
  | cons i s ih =>
    rw [List.flatMap_cons, List.foldl_append, apply_repeated_label, ih]
    simp [mul_assoc]

/-- A single digit raises the previous accumulator to the field cardinality and
then multiplies by the label monomial of this digit. -/
theorem digitSteps_eval (X : Fin t → A) (d : Fin t → ℕ) (v : A) :
    (digitSteps K X d).foldl (fun a M => M a) v =
      v ^ Fintype.card K * ∏ i, X i ^ d i := by
  rw [digitSteps, List.foldl_cons, apply_label_digits, Fin.prod_univ_def]
  rfl

private lemma digitProgram_eval_of_lt (X : Fin t → A) (width : ℕ) (e : Fin t → ℕ)
    (h : ∀ i, e i < Fintype.card K ^ width) :
    (digitProgram K X width e).foldl (fun a M => M a) 1 = ∏ i, X i ^ e i := by
  induction width generalizing e with
  | zero =>
    have he : ∀ i, e i = 0 := fun i => Nat.lt_one_iff.mp (by simpa using h i)
    simp [digitProgram, he]
  | succ width ih =>
    have hdiv (i : Fin t) : e i / Fintype.card K < Fintype.card K ^ width :=
      (Nat.div_lt_iff_lt_mul Fintype.card_pos).mpr (by simpa [pow_succ] using h i)
    rw [digitProgram, List.foldl_append, ih _ hdiv, digitSteps_eval,
      ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_add, Nat.mul_comm (e i / Fintype.card K), Nat.div_add_mod]

/-- For exponents given by `width` input bits, `width` base-`#K` digits suffice.
Starting the linear program at the unit returns the entire label monomial. -/
theorem digitProgram_eval (X : Fin t → A) (width : ℕ) (e : Fin t → ℕ)
    (h : ∀ i, e i < 2 ^ width) :
    (digitProgram K X width e).foldl (fun a M => M a) 1 = ∏ i, X i ^ e i :=
  digitProgram_eval_of_lt K X width e fun i =>
    (h i).trans_le (Nat.pow_le_pow_left (Fintype.one_lt_card (α := K)) width)

/-- Number of linear steps, including the Frobenius step, for one digit. -/
theorem digitSteps_length (X : Fin t → A) (d : Fin t → ℕ) :
    (digitSteps K X d).length = 1 + ∑ i, d i := by
  simp [digitSteps, List.length_flatMap, Fin.sum_univ_def, Nat.add_comm]

/-- The linear program executes at most one Frobenius and `t * (#K - 1)` label
multiplications per input bit. -/
theorem digitProgram_length_le (X : Fin t → A) (width : ℕ) (e : Fin t → ℕ) :
    (digitProgram K X width e).length ≤ width * (1 + t * (Fintype.card K - 1)) := by
  induction width generalizing e with
  | zero => simp [digitProgram]
  | succ width ih =>
    have h (i : Fin t) : e i % Fintype.card K ≤ Fintype.card K - 1 := by
      have := Nat.mod_lt (e i) (Fintype.card_pos (α := K))
      omega
    have hsum : ∑ i, e i % Fintype.card K ≤ t * (Fintype.card K - 1) := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
    rw [digitProgram, List.length_append, digitSteps_length, Nat.succ_mul]
    exact Nat.add_le_add (ih _) (Nat.add_le_add_left hsum 1)

end Digits

section Paths

/-- One index guess for each matrix factor, with a unique path when there are no factors. -/
def IndexPath (ι : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => ι × IndexPath ι n

instance {ι : Type*} [Fintype ι] (n : ℕ) : Fintype (IndexPath ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI : Fintype (IndexPath ι n) := ih
    exact inferInstanceAs (Fintype (ι × IndexPath ι n))

variable {ι k : Type*} [Fintype ι] [DecidableEq ι]

/-- Product of entries along an index path. Ending at a different index contributes zero. -/
def pathWeight [Semiring k] :
    (ms : List (Matrix ι ι k)) → ι → ι → IndexPath ι ms.length → k
  | [], start, finish, _ => if start = finish then 1 else 0
  | m :: ms, start, finish, ⟨j, π⟩ => m start j * pathWeight ms j finish π

theorem sum_pathWeight [Semiring k] (ms : List (Matrix ι ι k)) (start finish : ι) :
    ∑ π, pathWeight ms start finish π = ms.prod start finish := by
  induction ms generalizing start with
  | nil =>
    change (∑ _ : PUnit, if start = finish then (1 : k) else 0) = (1 : Matrix ι ι k) start finish
    simp [Matrix.one_apply]
  | cons m ms ih =>
    change (∑ π : ι × IndexPath ι ms.length, m start π.1 * pathWeight ms π.1 finish π.2) =
      (m * ms.prod) start finish
    simp_rw [Fintype.sum_prod_type, ← Finset.mul_sum, ih, Matrix.mul_apply]

variable {p : ℕ} [Fact p.Prime] [Field k] [Algebra (ZMod p) k]

/-- Distinguish all index paths and all admissible final choices, including paths of equal weight. -/
abbrev AcceptingBranches (coord : k →ₗ[ZMod p] ZMod p) (ms : List (Matrix ι ι k))
    (start finish : ι) :=
  (π : IndexPath ι ms.length) × Fin (coord (pathWeight ms start finish π)).val

/-- The integer path count, reduced modulo the prime, equals the prime-field coordinate of the
matrix product entry. The coordinate is applied once to the product of entries on each path. -/
theorem card_acceptingBranches_cast (coord : k →ₗ[ZMod p] ZMod p)
    (ms : List (Matrix ι ι k)) (start finish : ι) :
    (Fintype.card (AcceptingBranches coord ms start finish) : ZMod p) =
      coord (ms.prod start finish) := by
  rw [← sum_pathWeight ms start finish, map_sum]
  simp [AcceptingBranches, Fintype.card_sigma, Nat.cast_sum]
  rfl

end Paths

section Basis

variable {I K A : Type*} [Field K] [CommRing A] [Algebra K A]
variable [Fintype I] [DecidableEq I]

/-- At a step from index `i` to `j`, read row `j`, column `i` of the
matrix of the linear map. Transposing puts these entries in path order. -/
noncomputable def transitionMatrices (b : Module.Basis I K A)
    (steps : List (A →ₗ[K] A)) : List (Matrix I I K) :=
  steps.map (fun f => (LinearMap.toMatrixAlgEquiv b f).transpose)

private theorem transition_product (b : Module.Basis I K A) (steps : List (A →ₗ[K] A)) :
    (transitionMatrices b steps).prod.transpose =
      LinearMap.toMatrixAlgEquiv b steps.reverse.prod := by
  induction steps with
  | nil => simp [transitionMatrices]
  | cons f fs ih =>
    simp only [transitionMatrices, List.map_cons, List.prod_cons, Matrix.transpose_mul,
      Matrix.transpose_transpose, List.reverse_cons, List.prod_append, List.prod_nil, mul_one,
      map_mul]
    rw [← ih]
    rfl

private theorem reverse_prod_apply (steps : List (A →ₗ[K] A)) (a : A) :
    steps.reverse.prod a = steps.foldl (fun v f => f v) a := by
  induction steps generalizing a with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_singleton, List.foldl_cons,
      Module.End.mul_apply]
    exact ih (f a)

/-- The matrix product entry from the basis element `1` to itself gives its
coordinate after the chronological sequence of linear maps. -/
theorem transitionMatrices_unit_entry (b : Module.Basis I K A) (u : I) (hunit : b u = 1)
    (steps : List (A →ₗ[K] A)) :
    (transitionMatrices b steps).prod u u = b.coord u (steps.foldl (fun v f => f v) 1) := by
  have h := congrArg (fun M : Matrix I I K => M u u) (transition_product b steps)
  simpa only [Matrix.transpose_apply, LinearMap.toMatrixAlgEquiv_apply, hunit, reverse_prod_apply,
    Module.Basis.coord_apply] using h

variable {p : ℕ} [Fact p.Prime]
variable [Algebra (ZMod p) K] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A]

/-- The first coordinate over the slice field, followed by a prime-field
coordinate. This is the functional of Theorem 8.1. -/
noncomputable def primeFunctional (b : Module.Basis I K A) (u : I) (coord : K →ₗ[ZMod p] ZMod p) :
    A →ₗ[ZMod p] ZMod p :=
  coord.comp ((b.coord u).restrictScalars (ZMod p))

omit [Fintype I] [DecidableEq I] in
theorem primeFunctional_one (b : Module.Basis I K A) (u : I) (hunit : b u = 1)
    (coord : K →ₗ[ZMod p] ZMod p) (hcoord : coord 1 = 1) :
    primeFunctional b u coord 1 = 1 := by
  simp [primeFunctional, ← hunit, Module.Basis.coord_apply, hcoord]

end Basis

/-- Equation (8.2). For every vector of exponents fitting in `width` bits,
the integer number of accepting branches reduces to the prime-field
functional of the entire monomial. -/
theorem finiteAlgebra_pathCount {p : ℕ} [Fact p.Prime] {K A I : Type*}
    [Field K] [Fintype K] [CommRing A] [Algebra K A]
    [Algebra (ZMod p) K] [Algebra (ZMod p) A] [IsScalarTower (ZMod p) K A]
    [Fintype I] [DecidableEq I] (b : Module.Basis I K A) (u : I) (hunit : b u = 1)
    (coord : K →ₗ[ZMod p] ZMod p) {t : ℕ} (X : Fin t → A) (width : ℕ) (e : Fin t → ℕ)
    (hwidth : ∀ i, e i < 2 ^ width) :
    (Fintype.card (AcceptingBranches coord (transitionMatrices b (digitProgram K X width e)) u u) :
        ZMod p) = primeFunctional b u coord (∏ i, X i ^ e i) := by
  rw [card_acceptingBranches_cast, transitionMatrices_unit_entry b u hunit,
    digitProgram_eval _ _ _ _ hwidth]
  rfl

end Evaluator

end VPVNP
end Computability
end OAI
