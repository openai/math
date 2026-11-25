import OAI.LinearAlgebra.FiniteFourier.GeometricMatrix
import OAI.Computability.FourierCircuit.Triangular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! # Newton factorization of geometric evaluation matrices -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Matrix Polynomial
open scoped Matrix

variable {K : Type*}

section Ring

variable [CommRing K]

/-- The monic Newton polynomial in column `j` of the change of basis. -/
noncomputable def geometricNewtonPolynomial (q : K) (j : ℕ) : K[X] :=
  ∏ k ∈ range j, (X - C (q ^ k))

/-- Evaluation in the Newton basis at the geometric nodes. -/
def geometricNewtonMatrix (a : ℕ) (q : K) : Matrix (Fin a) (Fin a) K :=
  Matrix.of fun i j ↦ ∏ k ∈ range j.val, (q ^ i.val - q ^ k)

/-- Product of the first `i` factors `1-q^k`, starting at `k=1`. -/
def geometricFactorial (q : K) (i : ℕ) : K :=
  ∏ k ∈ range i, (1 - q ^ (k + 1))

def newtonColumnFactor (q : K) (j : ℕ) : K :=
  (-1) ^ j * q ^ (j.choose 2)

lemma geometricNewton_cross (q : K) (i j : ℕ) (hji : j ≤ i) :
    (∏ k ∈ range j, (q ^ i - q ^ k)) * geometricFactorial q (i - j) =
      newtonColumnFactor q j * geometricFactorial q i := by
  induction j with
  | zero => simp [newtonColumnFactor]
  | succ j ih =>
    have hj : j ≤ i := by omega
    have he : i - j = i - (j + 1) + 1 := by omega
    have hH : geometricFactorial q (i - j) =
        geometricFactorial q (i - (j + 1)) * (1 - q ^ (i - j)) := by
      conv_lhs => rw [he]
      unfold geometricFactorial
      rw [prod_range_succ, ← he]
    have hx : q ^ i - q ^ j = -(q ^ j) * (1 - q ^ (i - j)) := by
      conv_lhs => lhs; rw [← Nat.add_sub_of_le hj, pow_add]
      ring
    have hcol : newtonColumnFactor q (j + 1) = newtonColumnFactor q j * -(q ^ j) := by
      simp [newtonColumnFactor, Nat.choose_succ_succ, pow_succ, pow_add]
      ring
    rw [prod_range_succ, hx, hcol]
    calc
      _ = -(q ^ j) * ((∏ k ∈ range j, (q ^ i - q ^ k)) * geometricFactorial q (i - j)) := by
        rw [hH]; ring
      _ = _ := by rw [ih hj]; ring

/-- Newton evaluation is lower triangular. -/
theorem geometricNewtonMatrix_lower (a : ℕ) (q : K) :
    (geometricNewtonMatrix a q).IsLowerTriangular := by
  intro i j hij
  apply prod_eq_zero (mem_range.mpr (show i.val < j.val from hij))
  exact sub_self _

end Ring

section Field

variable [Field K]

theorem geometricFactorial_ne_zero {a : ℕ} {q : K}
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) {i : ℕ} (hi : i < a) :
    geometricFactorial q i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk hkzero
  have hk' : k + 1 < a := by have := mem_range.mp hk; omega
  have heq : (⟨0, by omega⟩ : Fin a) = ⟨k+1, hk'⟩ := hd (by simpa using sub_eq_zero.mp hkzero)
  have := congrArg Fin.val heq
  simp at this

/-- Lower-triangular entries of the Newton evaluation matrix in closed form. -/
theorem geometricNewtonMatrix_entry {a : ℕ} (q : K)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) (i j : Fin a) (hji : j ≤ i) :
    geometricNewtonMatrix a q i j =
      (-1) ^ j.val * q ^ (j.val.choose 2) * geometricFactorial q i.val /
      geometricFactorial q (i.val - j.val) := by
  apply (eq_div_iff (geometricFactorial_ne_zero hd (Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt))).mpr
  exact geometricNewton_cross q _ _ hji

private theorem newton_diag_ne_zero {a : ℕ} (q : K)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) (i : Fin a) :
    geometricNewtonMatrix a q i i ≠ 0 := by
  change (∏ k ∈ range i.val, (q ^ i.val - q ^ k)) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk h
  have hk' := mem_range.mp hk
  have heq : i = ⟨k, hk'.trans i.isLt⟩ := hd (sub_eq_zero.mp h)
  have := congrArg Fin.val heq
  exact hk'.ne (show i.val = k from this).symm

end Field

section RingFactorization

variable [CommRing K] [Nontrivial K]

/-- The symmetric geometric Vandermonde factors through its Newton evaluations,
with the diagonal of these evaluations supplying the middle pivot matrix. -/
theorem geometric_newton_factorization_of_unit_pivots {a : ℕ} (q : K)
    (hu : ∀ i, IsUnit (geometricNewtonMatrix a q i i)) :
    let L := geometricNewtonMatrix a q
    geometricMatrix a q = L * (diagonal (fun i ↦ L i i))⁻¹ * Lᵀ := by
  classical
  let L := geometricNewtonMatrix a q
  let V := geometricMatrix a q
  let p := fun (j : Fin a) ↦ geometricNewtonPolynomial q j.val
  let P := Matrix.of (fun (i j : Fin a) ↦ (p j).coeff i.val)
  let D := diagonal (fun i ↦ L i i)
  have hdeg (i : Fin a) : (p i).natDegree = i.val := by
    exact (natDegree_finsetProd_X_sub_C_eq_card (range i.val) (fun k ↦ q ^ k)).trans (card_range _)
  have hmon (i : Fin a) : (p i).Monic := monic_prod_X_sub_C _ _
  have hVP : V * P = L := by
    rw [show V * P = Matrix.of (fun i j ↦ (p j).eval (q ^ i.val)) from
      (eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials _ p (fun i ↦ (hdeg i).le)).symm]
    ext i j
    simp [p, L, geometricNewtonPolynomial, geometricNewtonMatrix, Polynomial.eval_prod]
  have hP : P.IsUpperTriangular :=
    matrixOfPolynomials_isUpperTriangular p (fun i ↦ (hdeg i).le)
  have hL : L.IsLowerTriangular := geometricNewtonMatrix_lower a q
  have hPl : Pᵀ.IsLowerTriangular := hP.transpose
  have hV : Vᵀ = V := by
    ext i j
    simp [V, geometricMatrix, vandermonde_apply, ← pow_mul, Nat.mul_comm]
  have hLt : Lᵀ = Pᵀ * V := by rw [← hVP, transpose_mul, hV]
  have hsym : (Pᵀ * L)ᵀ = Pᵀ * L := by rw [transpose_mul, transpose_transpose, hLt, Matrix.mul_assoc, hVP]
  have hdiag : Pᵀ * L = D := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [(hPl.mul hL) hij]
      simp [D, hij.ne]
    · rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp [P, D, ← hdeg i, (hmon i).coeff_natDegree]
      · intro k _ hki
        rcases lt_or_gt_of_ne hki with hk | hk
        · simp [hL (i := k) (j := i) hk]
        · simp [Matrix.transpose_apply, hP (i := k) (j := i) hk]
      · simp
    · rw [← congrFun (congrFun hsym i) j, transpose_apply, (hPl.mul hL) hji]
      simp [D, hji.ne']
  have hdu : IsUnit D.det := by
    rw [Matrix.det_diagonal]
    exact IsUnit.prod_univ_iff.mpr hu
  have hleft : (D⁻¹ * Lᵀ) * P = 1 := by
    rw [Matrix.mul_assoc, hLt, Matrix.mul_assoc, hVP, hdiag, Matrix.nonsing_inv_mul _ hdu]
  have hright : P * (D⁻¹ * Lᵀ) = 1 := mul_eq_one_comm.mp hleft
  change V = L * D⁻¹ * Lᵀ
  calc
    V = V * (P * (D⁻¹ * Lᵀ)) := by rw [hright, Matrix.mul_one]
    _ = L * D⁻¹ * Lᵀ := by rw [← Matrix.mul_assoc, hVP, Matrix.mul_assoc]

end RingFactorization

section Field

variable [Field K]

/-- Distinct nodes give the unit pivots of the Newton decomposition over a field. -/
theorem geometric_newton_factorization {a : ℕ} (q : K)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
    let L := geometricNewtonMatrix a q
    geometricMatrix a q = L * (diagonal (fun i ↦ L i i))⁻¹ * Lᵀ :=
  geometric_newton_factorization_of_unit_pivots q fun i ↦ (newton_diag_ne_zero q hd i).isUnit

open ExactFourier.CoefficientTime

/-- Inverting a triangular Toeplitz matrix amounts to taking a reciprocal power series. -/
theorem lowerToeplitz_inv (a : ℕ) (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) :
    (truncMatrix a f)⁻¹ = truncMatrix a f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← truncMatrix_mul, PowerSeries.mul_inv_cancel _ hf, truncMatrix_one]

/-- Newton evaluation is diagonally equivalent to a lower triangular Toeplitz
matrix with constant coefficient one. -/
theorem geometricNewtonMatrix_toeplitz {a : ℕ} (q : K)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val)) :
    geometricNewtonMatrix a q =
      diagonal (fun i : Fin a ↦ geometricFactorial q i.val) *
      truncMatrix a (PowerSeries.mk (fun k ↦ (geometricFactorial q k)⁻¹)) *
      diagonal (fun i : Fin a ↦ (-1) ^ i.val * q ^ (i.val.choose 2)) := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hji : j.val ≤ i.val
  · rw [geometricNewtonMatrix_entry q hd i j hji]
    simp [truncMatrix, hji, div_eq_mul_inv, mul_comm, mul_assoc]
  · rw [geometricNewtonMatrix_lower a q (i := i) (j := j) (lt_of_not_ge hji)]
    simp [truncMatrix, hji]

/-- The permitted invertible factors in the geometric Newton factorization. -/
inductive IsGridDiagonalOrToeplitz {a : ℕ} : Matrix (Fin a) (Fin a) K → Prop
  | diagonal (v : Fin a → K) (hv : ∀ i, v i ≠ 0) : IsGridDiagonalOrToeplitz (Matrix.diagonal v)
  | lower (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) : IsGridDiagonalOrToeplitz (truncMatrix a f)
  | upper (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) : IsGridDiagonalOrToeplitz (truncMatrix a f)ᵀ

theorem IsGridDiagonalOrToeplitz.isUnit {a : ℕ} {A : Matrix (Fin a) (Fin a) K}
    (h : IsGridDiagonalOrToeplitz A) : IsUnit A := by
  cases h with
  | diagonal v hv => exact Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i ↦ (hv i).isUnit))
  | lower f hf => exact trunc_isUnit a f hf.isUnit
  | upper f hf => exact (Matrix.isUnit_transpose _).mpr (trunc_isUnit a f hf.isUnit)

theorem IsGridDiagonalOrToeplitz.inv {a : ℕ} {A : Matrix (Fin a) (Fin a) K}
    (h : IsGridDiagonalOrToeplitz A) : IsGridDiagonalOrToeplitz A⁻¹ := by
  cases h with
  | diagonal v hv =>
    rw [Matrix.inv_diagonal]
    have hu : IsUnit v := Pi.isUnit_iff.mpr fun i ↦ (hv i).isUnit
    apply IsGridDiagonalOrToeplitz.diagonal
    intro i
    have hunit := congrFun (Ring.inverse_mul_cancel v hu) i
    exact left_ne_zero_of_mul_eq_one hunit
  | lower f hf =>
    rw [lowerToeplitz_inv _ f hf]
    exact .lower _ (by simpa using hf)
  | upper f hf =>
    rw [← Matrix.transpose_nonsing_inv, lowerToeplitz_inv _ f hf]
    exact .upper _ (by simpa using hf)

/-- Both a geometric evaluation matrix and its inverse are products of at most
seven invertible diagonal and triangular Toeplitz factors over the original field. -/
theorem geometricMatrix_and_inverse_factors {a : ℕ} (q : K) (hq : q ≠ 0)
    (hd : Function.Injective (fun i : Fin a ↦ q ^ i.val))
    (A : Matrix (Fin a) (Fin a) K) (hA : A = geometricMatrix a q ∨ A = (geometricMatrix a q)⁻¹) :
    ∃ factors : List (Matrix (Fin a) (Fin a) K), factors.length ≤ 7 ∧
      (∀ B ∈ factors, IsGridDiagonalOrToeplitz B) ∧ factors.prod = A := by
  let b : Fin a → K := fun i ↦ geometricFactorial q i.val
  let c : Fin a → K := fun i ↦ (-1) ^ i.val * q ^ (i.val.choose 2)
  let f : PowerSeries K := PowerSeries.mk fun k ↦ (geometricFactorial q k)⁻¹
  let d : Fin a → K := fun i ↦ geometricNewtonMatrix a q i i
  let factors := [diagonal b, truncMatrix a f, diagonal c, (diagonal d)⁻¹,
                  diagonal c, (truncMatrix a f)ᵀ, diagonal b]
  have hf : f.constantCoeff ≠ 0 := by simp [f, geometricFactorial, PowerSeries.constantCoeff_mk]
  have hb : IsGridDiagonalOrToeplitz (diagonal b) := .diagonal _ (fun i ↦ geometricFactorial_ne_zero hd i.isLt)
  have hc : IsGridDiagonalOrToeplitz (diagonal c) :=
    .diagonal _ (fun i ↦ mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hq))
  have hD : IsGridDiagonalOrToeplitz (diagonal d) :=
    .diagonal _ (newton_diag_ne_zero q hd)
  have Hall : ∀ B ∈ factors, IsGridDiagonalOrToeplitz B := by
    simp [factors, hb, hc, hD.inv, IsGridDiagonalOrToeplitz.lower f hf,
      IsGridDiagonalOrToeplitz.upper f hf]
  have hprod : factors.prod = geometricMatrix a q := by
    have h := geometric_newton_factorization q hd
    change geometricMatrix a q = geometricNewtonMatrix a q * (diagonal d)⁻¹ *
      (geometricNewtonMatrix a q)ᵀ at h
    have hl : geometricNewtonMatrix a q = diagonal b * truncMatrix a f * diagonal c :=
      geometricNewtonMatrix_toeplitz q hd
    rw [h, hl]
    simp [factors, Matrix.transpose_mul, Matrix.mul_assoc]
  rcases hA with rfl | rfl
  · exact ⟨factors, by simp [factors], Hall, hprod⟩
  · refine ⟨factors.reverse.map Inv.inv, by simp [factors], ?_, ?_⟩
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact (Hall C (List.mem_reverse.mp hC)).inv
    · rw [← Matrix.list_prod_inv_reverse, hprod]

end Field

end FiniteFourier
end LinearAlgebra
end OAI
