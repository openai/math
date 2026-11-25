import OAI.LinearAlgebra.FiniteFourier.GeometricNewton
import OAI.LinearAlgebra.FiniteFourier.ProtectedShears

/-! # Newton factors over a protected coefficient domain

All inverses in the geometric Newton factorization are inverses of units of
the original ring. In particular the Fourier and inverse Fourier transforms
at a primitive root of unit order admit factorizations over that same ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Matrix ExactFourier.CoefficientTime
open scoped Ring Matrix

variable {R : Type*} [CommRing R] {a : ℕ}

/-- The three kinds of protected factors. Lower and upper triangular Toeplitz
factors are normalized to have diagonal one. -/
inductive ProtectedNewtonFactor : Matrix (Fin a) (Fin a) R → Prop where
  | diagonal (d : Fin a → R) (hd : ∀ i, IsUnit (d i)) :
      ProtectedNewtonFactor (Matrix.diagonal d)
  | lower (f : PowerSeries R) (hf : f.constantCoeff = 1) :
      ProtectedNewtonFactor (truncMatrix a f)
  | upper (f : PowerSeries R) (hf : f.constantCoeff = 1) :
      ProtectedNewtonFactor (truncMatrix a f)ᵀ

private theorem inverse_unitriangular_toeplitz (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    (truncMatrix a f)⁻¹ = truncMatrix a (f.invOfUnit 1) := by
  apply Matrix.inv_eq_right_inv
  rw [← truncMatrix_mul, PowerSeries.mul_invOfUnit f 1 (by simpa using hf), truncMatrix_one]

theorem ProtectedNewtonFactor.inv {A : Matrix (Fin a) (Fin a) R}
    (h : ProtectedNewtonFactor A) : ProtectedNewtonFactor A⁻¹ := by
  cases h with
  | diagonal d hd =>
    rw [Matrix.inv_diagonal]
    exact .diagonal _ (Pi.isUnit_iff.mp (Pi.isUnit_iff.mpr hd).ringInverse)
  | lower f hf =>
    rw [inverse_unitriangular_toeplitz f hf]
    exact .lower _ (by simp [PowerSeries.constantCoeff_invOfUnit])
  | upper f hf =>
    rw [← Matrix.transpose_nonsing_inv, inverse_unitriangular_toeplitz f hf]
    exact .upper _ (by simp [PowerSeries.constantCoeff_invOfUnit])

/-- Newton evaluation splits into a pair of invertible scalings and one
unitriangular Toeplitz factor whenever the geometric factorials are units. -/
theorem protectedNewtonMatrix_toeplitz (q : R)
    (hfact : ∀ k < a, IsUnit (geometricFactorial q k)) :
    geometricNewtonMatrix a q =
      diagonal (fun i : Fin a ↦ geometricFactorial q i.val) *
      truncMatrix a (PowerSeries.mk fun k ↦ (geometricFactorial q k)⁻¹ʳ) *
      diagonal (fun i : Fin a ↦ newtonColumnFactor q i.val) := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  by_cases hji : j.val ≤ i.val
  · simp only [truncMatrix, hji, ite_true, PowerSeries.coeff_mk]
    rw [mul_right_comm]
    apply (Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hfact _ ((Nat.sub_le _ _).trans_lt i.isLt))).mpr
    rw [mul_comm (geometricFactorial _ _)]
    exact geometricNewton_cross q i.val j.val hji
  · rw [geometricNewtonMatrix_lower a q (i := i) (j := j) (lt_of_not_ge hji)]
    simp [truncMatrix, hji]

/-- The geometric evaluations at unit-separated powers of a unit split into
seven protected factors in either direction. The coefficient ring may have
zero divisors, as it does in the jet extension. -/
theorem protectedGeometric_and_inverse_factors [Nontrivial R] {q : R} (hq : IsUnit q)
    (hsep : Pairwise fun i j : Fin a ↦ IsUnit (q ^ i.val - q ^ j.val))
    (A : Matrix (Fin a) (Fin a) R)
    (hA : A = geometricMatrix a q ∨ A = (geometricMatrix a q)⁻¹) :
    ∃ factors : List (Matrix (Fin a) (Fin a) R), factors.length = 7 ∧
      (∀ B ∈ factors, ProtectedNewtonFactor B) ∧ factors.prod = A := by
  classical
  have hfact (k : ℕ) (hk : k < a) : IsUnit (geometricFactorial q k) := by
    apply IsUnit.prod_iff.mpr
    intro j hj
    have hj' := mem_range.mp hj
    let s : Fin a := ⟨0, by omega⟩
    let t : Fin a := ⟨j+1, by omega⟩
    have hst : s ≠ t := fun eq ↦ Nat.succ_ne_zero j (congrArg Fin.val eq).symm
    simpa [s, t] using hsep hst
  let b (i : Fin a) := geometricFactorial q i.val
  let c (i : Fin a) := newtonColumnFactor q i.val
  let f : PowerSeries R := PowerSeries.mk fun k ↦ (geometricFactorial q k)⁻¹ʳ
  let d (i : Fin a) := geometricNewtonMatrix a q i i
  have hc (i : Fin a) : IsUnit (c i) :=
    (isUnit_one.neg.pow _).mul (hq.pow _)
  have hd (i : Fin a) : IsUnit (d i) := by
    have he := geometricNewton_cross q i.val i.val le_rfl
    simp only [Nat.sub_self, geometricFactorial, prod_range_zero, mul_one] at he
    change IsUnit (∏ k ∈ range i.val, (q ^ i.val - q ^ k))
    rw [he]
    exact (hc i).mul (hfact i.val i.isLt)
  let l := [diagonal b, truncMatrix a f, diagonal c, (diagonal d)⁻¹,
            diagonal c, (truncMatrix a f)ᵀ, diagonal b]
  have hf : f.constantCoeff = 1 := by simp [f, geometricFactorial, PowerSeries.constantCoeff_mk]
  have hb' : ProtectedNewtonFactor (diagonal b) := .diagonal _ fun i ↦ hfact i.val i.isLt
  have hc' : ProtectedNewtonFactor (diagonal c) := .diagonal _ hc
  have hd' : ProtectedNewtonFactor (diagonal d) := .diagonal _ hd
  have hall : ∀ B ∈ l, ProtectedNewtonFactor B := by
    simp [l, hb', hc', hd'.inv, ProtectedNewtonFactor.lower f hf, ProtectedNewtonFactor.upper f hf]
  have hp : l.prod = geometricMatrix a q := by
    have h := geometric_newton_factorization_of_unit_pivots q hd
    change geometricMatrix a q = geometricNewtonMatrix a q * (diagonal d)⁻¹ *
      (geometricNewtonMatrix a q)ᵀ at h
    have hl : geometricNewtonMatrix a q = diagonal b * truncMatrix a f * diagonal c :=
      protectedNewtonMatrix_toeplitz q hfact
    rw [h, hl]
    simp [l, Matrix.transpose_mul, Matrix.mul_assoc]
  rcases hA with rfl | rfl
  · exact ⟨l, rfl, hall, hp⟩
  · refine ⟨l.reverse.map Inv.inv, by simp [l], ?_, ?_⟩
    · intro B hB
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
      exact (hall C (List.mem_reverse.mp hC)).inv
    · rw [← Matrix.list_prod_inv_reverse, hp]

/-- A primitive root with unit order supplies unit separation in a protected
domain. All seven factors of either transform lie in this domain. -/
theorem protectedFourier_and_inverse_factors [IsDomain R] {q : R} (hq : IsPrimitiveRoot q a)
    (ha : IsUnit (a : R)) (A : Matrix (Fin a) (Fin a) R)
    (hA : A = geometricMatrix a q ∨ A = (geometricMatrix a q)⁻¹) :
    ∃ factors : List (Matrix (Fin a) (Fin a) R), factors.length = 7 ∧
      (∀ B ∈ factors, ProtectedNewtonFactor B) ∧ factors.prod = A := by
  have hap : 0 < a := Nat.pos_of_ne_zero fun h ↦ ha.ne_zero (by simp [h])
  apply protectedGeometric_and_inverse_factors (hq.isUnit hap.ne') _ A hA
  have hlt (i j : Fin a) (h : i < j) : IsUnit (q ^ i.val - q ^ j.val) := by
    have hdiff := newtonFactor_isUnit hq ha (j := j.val-i.val)
      (Nat.sub_pos_of_lt h) ((Nat.sub_le _ _).trans_lt j.isLt)
    convert ((hq.isUnit hap.ne').pow i.val).mul hdiff using 1
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le h.le]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · simpa [neg_sub] using (hlt j i h).neg

end FiniteFourier
end LinearAlgebra
end OAI
