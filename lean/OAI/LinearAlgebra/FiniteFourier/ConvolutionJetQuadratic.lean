import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.Ring
import OAI.LinearAlgebra.FiniteFourier.OpenConvolution
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel

/-! # Common quadratic projections for a packed jet product

For a coefficient written in the basis `1, η`, use the same three input rows
on both sides of each ordinary base-ring convolution. The decoder uses only
the two coefficients of the relation `η² = c + η d`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial
open scoped Classical

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The common input rows of the three convolution children. -/
def quadraticRow {M : Type*} [Add M] (x y : M) (j : Fin 3) : M :=
  if j = 0 then x else if j = 1 then y else x + y

/-- The two base-ring output coordinates for a quadratic generator with
relation `η² = c + η d`. -/
def quadraticDecode {A : Type*} [Ring A] (c d : A) (p : Fin 3 → A) : A × A :=
  (p 0 + c * p 1, p 2 - p 0 - p 1 + d * p 1)

/-- Interpret a pair of base-ring polynomials coefficientwise in the power basis. -/
noncomputable def quadraticPolynomial (φ : R →+* S) (η : S) (u v : R[X]) : S[X] :=
  u.map φ + C η * v.map φ

theorem quadraticPolynomial_coeff (φ : R →+* S) (η : S) (u v : R[X]) (k : ℕ) :
    (quadraticPolynomial φ η u v).coeff k = φ (u.coeff k) + η * φ (v.coeff k) := by
  simp [quadraticPolynomial, coeff_map, coeff_C_mul]

/-- All three projected packed operands fit in the original operand length. -/
theorem quadraticRow_natDegree_lt {n : ℕ} {u v : R[X]} (hu : u.natDegree < n)
    (hv : v.natDegree < n) (j : Fin 3) : (quadraticRow u v j).natDegree < n := by
  unfold quadraticRow
  split <;> first | assumption | split
  · exact hv
  · exact (natDegree_add_le _ _).trans_lt (max_lt hu hv)

/-- The coefficient of a row is the same projection applied to that coefficient. -/
theorem quadraticRow_coeff (u v : R[X]) (j : Fin 3) (k : ℕ) :
    (quadraticRow u v j).coeff k = quadraticRow (u.coeff k) (v.coeff k) j := by
  unfold quadraticRow
  split <;> first | rfl | split <;> simp

/-- Three base-ring polynomial products reconstruct the packed product in the
quadratic algebra, including its reduction by the monic quadratic relation. -/
theorem quadraticPolynomial_mul (φ : R →+* S) (η : S) (c d : R)
    (hη : η ^ 2 = φ c + η * φ d) (u₀ u₁ v₀ v₁ : R[X]) :
    let p := fun j => quadraticRow u₀ u₁ j * quadraticRow v₀ v₁ j
    let q := quadraticDecode (C c) (C d) p
    quadraticPolynomial φ η q.1 q.2 =
      quadraticPolynomial φ η u₀ u₁ * quadraticPolynomial φ η v₀ v₁ := by
  have hc : (C η : S[X]) ^ 2 = C (φ c) + C η * C (φ d) := by
    rw [← map_pow, hη, map_add, map_mul]
  simp [quadraticPolynomial, quadraticDecode, quadraticRow, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul]
  linear_combination -(u₁.map φ * v₁.map φ) * hc

/-- The ordinary open convolution gates of the circuit model give exactly the
coefficients of the three polynomial products. -/
theorem ofFn_mul_coeff_openConv {n : ℕ} (x y : Fin n → R) (k : Fin (2*n-1)) :
    (ofFn n x * ofFn n y).coeff k = openConv R n x y k := by
  classical
  simp only [ofFn_eq_sum_monomial, Finset.sum_mul, Finset.mul_sum, finsetSum_coeff,
    monomial_mul_monomial, coeff_monomial, openConv]
  exact Finset.sum_comm

/-- The two decoded scalar outputs at each index recover the actual product
coefficient using three untruncated base-ring convolutions of the same length. -/
theorem quadratic_openConv_coeff (φ : R →+* S) (η : S) (c d : R)
    (hη : η ^ 2 = φ c + η * φ d) {n : ℕ} (x₀ x₁ y₀ y₁ : Fin n → R)
    (k : Fin (2*n-1)) :
    let p := fun j => openConv R n (fun i => quadraticRow (x₀ i) (x₁ i) j)
      (fun i => quadraticRow (y₀ i) (y₁ i) j) k
    let q := quadraticDecode c d p
    φ q.1 + η * φ q.2 =
      (quadraticPolynomial φ η (ofFn n x₀) (ofFn n x₁) *
       quadraticPolynomial φ η (ofFn n y₀) (ofFn n y₁)).coeff k := by
  classical
  dsimp only
  rw [← quadraticPolynomial_mul φ η c d hη, quadraticPolynomial_coeff]
  have hrow (x y : Fin n → R) (j : Fin 3) :
      quadraticRow (ofFn n x) (ofFn n y) j = ofFn n (fun i => quadraticRow (x i) (y i) j) := by
    unfold quadraticRow
    split
    · rfl
    · split
      · rfl
      · exact (map_add (ofFn n) x y).symm
  simp only [quadraticDecode, coeff_add, coeff_sub, coeff_C_mul, hrow, ofFn_mul_coeff_openConv]

/-- One addition supplies all three projections of one quadratic coefficient. -/
private def quadraticInputGate (R : Type*) [CommRing R] : Circuit R (Fin 2) (Fin 3) 1 where
  program := Program.nil.step ⟨.inl 0, .inl 1, 1, 1⟩
  output j := if j = 0 then .scaled 1 (.inl 0) else if j = 1 then .scaled 1 (.inl 1)
    else .scaled 1 (.inr 0)

private theorem quadraticInputGate_eval (x : Fin 2 → R) (j : Fin 3) :
    (quadraticInputGate R).eval x j = quadraticRow (x 0) (x 1) j := by
  fin_cases j <;> simp [Circuit.eval, quadraticInputGate, quadraticRow, Readout.eval,
    Program.value, BinaryGate.eval]

/-- Three binary linear gates compute both output coordinates. -/
private def quadraticOutputGates (c d : R) : Circuit R (Fin 3) (Fin 2) 3 where
  program := ((Program.nil.step ⟨.inl 0, .inl 1, 1, c⟩).step
    ⟨.inl 2, .inl 0, 1, -1⟩).step ⟨.inr 0, .inl 1, 1, d-1⟩
  output j := if j = 0 then .scaled 1 (.inr (0 : Fin 1).succ.succ) else .scaled 1 (.inr 0)

private theorem quadraticOutputGates_eval (c d : R) (p : Fin 3 → R) (j : Fin 2) :
    (quadraticOutputGates c d).eval p j =
      if j = 0 then (quadraticDecode c d p).1 else (quadraticDecode c d p).2 := by
  fin_cases j
  · change 1 * (1 * p 0 + c * p 1) = p 0 + c * p 1
    simp
  · change 1 * (1 * (1 * p 2 + -1 * p 0) + (d-1) * p 1) = p 2 - p 0 - p 1 + d * p 1
    ring

/-- The common encoder and decoder over the base ring use at most one gate per
input position and three gates per output position, respectively. -/
theorem exists_quadratic_convolution_circuits (c d : R) (n : ℕ) :
    ∃ (u v : ℕ) (enc : Circuit R (Σ _ : Fin n, Fin 2) (Σ _ : Fin n, Fin 3) u)
      (dec : Circuit R (Σ _ : Fin (2*n-1), Fin 3) (Σ _ : Fin (2*n-1), Fin 2) v),
      u ≤ n ∧ v ≤ 3*(2*n-1) ∧
      (∀ x (i : Fin n) (j : Fin 3),
        enc.eval x ⟨i, j⟩ = quadraticRow (x ⟨i, 0⟩) (x ⟨i, 1⟩) j) ∧
      (∀ p (k : Fin (2*n-1)) (j : Fin 2), dec.eval p ⟨k, j⟩ =
        if j = 0 then (quadraticDecode c d (fun s => p ⟨k,s⟩)).1
        else (quadraticDecode c d (fun s => p ⟨k,s⟩)).2) := by
  obtain ⟨u, hu, enc, henc⟩ := circuit_family fun _ : Fin n => quadraticInputGate R
  obtain ⟨v, hv, dec, hdec⟩ := circuit_family fun _ : Fin (2*n-1) => quadraticOutputGates c d
  refine ⟨u, v, enc, dec, by simpa using hu, by simpa [Nat.mul_comm] using hv, ?_, ?_⟩
  · intro x i j
    rw [henc, quadraticInputGate_eval]
    rfl
  · intro p k j
    rw [hdec, quadraticOutputGates_eval]
    rfl

end FiniteFourier
end LinearAlgebra
end OAI
