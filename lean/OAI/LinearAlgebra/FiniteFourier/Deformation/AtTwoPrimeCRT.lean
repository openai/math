import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock
import OAI.LinearAlgebra.FiniteFourier.QuadraticPeriods
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Splitting the scalar factor on a prime cyclic axis

Evaluation at one and reduction modulo the prime cyclotomic polynomial split the cyclic algebra
when the prime is a unit. In the two nonzero orbits, only the two constant frequencies interact
with the coefficient at the zero address.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Module
open scoped BigOperators

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]

private theorem cyclotomic_eval_one_prime : (cyclotomic p R).eval 1 = p := by
  simp [cyclotomic_prime R p]

private theorem cyclotomic_mul_linear :
    cyclotomic p R * (X - C (1 : R)) = X ^ p - C 1 := by
  rw [cyclotomic_prime R p, C_1, geom_sum_mul]

private noncomputable def primeCyclicCRTHom :
    BinomialAxis p (1 : R) →ₐ[R] R × AdjoinRoot (cyclotomic p R) :=
  (AdjoinRoot.liftAlgHom _ (AlgHom.id R R) 1 (by simp)).prod
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId ..) (AdjoinRoot.root (cyclotomic p R))
      (by simp [primeAxis_pow]))

private theorem primeCyclicCRTHom_mk (q : R[X]) :
    primeCyclicCRTHom R p (AdjoinRoot.mk _ q) = (q.eval 1, AdjoinRoot.mk _ q) := by
  apply Prod.ext
  · rfl
  · exact AdjoinRoot.aeval_eq q

/-- The Chinese remainder isomorphism, in the order scalar then cyclotomic factor. -/
noncomputable def primeCyclicCRT (hp : IsUnit (p : R)) :
    BinomialAxis p (1 : R) ≃ₐ[R] R × AdjoinRoot (cyclotomic p R) := by
  apply AlgEquiv.ofBijective (primeCyclicCRTHom R p)
  constructor
  · intro a b hab
    obtain ⟨s, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨t, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [primeCyclicCRTHom_mk, primeCyclicCRTHom_mk, Prod.mk.injEq] at hab
    obtain ⟨hAtOne, hAtRoot⟩ := hab
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_mk.mp hAtRoot
    have hprod := congrArg (Polynomial.eval 1) hq
    rw [eval_sub, hAtOne, sub_self, eval_mul, cyclotomic_eval_one_prime] at hprod
    obtain ⟨g, hg⟩ := (dvd_iff_isRoot (p := q) (a := (1:R))).mpr
      ((hp.mul_right_eq_zero).mp hprod.symm)
    exact AdjoinRoot.mk_eq_mk.mpr ⟨g, by rw [hq, hg, ← mul_assoc, cyclotomic_mul_linear]⟩
  · rintro ⟨a, b⟩
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective b
    let k : R := (↑(hp.unit⁻¹) : R) * (a - f.eval 1)
    have hk : (p : R) * k = a - f.eval 1 := by
      dsimp [k]
      rw [← mul_assoc, hp.mul_val_inv, one_mul]
    refine ⟨AdjoinRoot.mk _ (f + cyclotomic p R * C k), ?_⟩
    rw [primeCyclicCRTHom_mk]
    simp only [eval_add, eval_mul, cyclotomic_eval_one_prime, eval_C, hk, add_sub_cancel,
      map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]

theorem primeCyclicCRT_mk (hp : IsUnit (p : R)) (q : R[X]) :
    primeCyclicCRT R p hp (AdjoinRoot.mk _ q) = (q.eval 1, AdjoinRoot.mk _ q) :=
  primeCyclicCRTHom_mk R p q

theorem primeCyclicCRT_root (hp : IsUnit (p : R)) :
    primeCyclicCRT R p hp (AdjoinRoot.root _) = (1, AdjoinRoot.root (cyclotomic p R)) := by
  simpa only [eval_X, AdjoinRoot.mk_X] using primeCyclicCRT_mk R p hp X

/-- The power basis of the cyclic algebra, indexed by its additive address group. -/
noncomputable def primeCyclicBasis [Nontrivial R] : Basis (ZMod p) R (BinomialAxis p (1 : R)) :=
  (binomialBasis (Fact.out : p.Prime).pos (1 : R)).reindex (ZMod.finEquiv p).toEquiv

theorem primeCyclicBasis_apply [Nontrivial R] (a : ZMod p) :
    primeCyclicBasis R p a = AdjoinRoot.root _ ^ a.val := by
  rw [primeCyclicBasis, Basis.reindex_apply, binomialBasis_apply]
  cases p with
  | zero => cases (Fact.out : Nat.Prime 0).ne_zero rfl
  | succ p => rfl

theorem primeCyclicBasis_add [Nontrivial R] (a b : ZMod p) :
    primeCyclicBasis R p (a+b) = primeCyclicBasis R p a * primeCyclicBasis R p b := by
  have h : AdjoinRoot.root ((X : R[X])^p - C 1) ^ p = 1 := by
    simpa using binomialAxis_root_pow p (1:R)
  simpa only [primeCyclicBasis_apply, AddChar.zmodChar_apply] using (AddChar.zmodChar p h).map_add_eq_mul a b

theorem primeCyclicCRT_basis [Nontrivial R] (hp : IsUnit (p : R)) (a : ZMod p) :
    primeCyclicCRT R p hp (primeCyclicBasis R p a) = (1, primeAxisCharacter R p a) := by
  rw [primeCyclicBasis_apply, map_pow, primeCyclicCRT_root]
  exact Prod.ext (one_pow _) rfl

section ZeroFrequency

variable {R} (m : ℕ)

/-- Change of coordinates from the scalar coefficient and two constant orbit modes
to the scalar factor and the ordered quadratic basis `1,U`. -/
def primeZeroFrequencyMatrix : Matrix (Fin 3) (Fin 3) R :=
  !![1, (m : R), m; 1, 0, -1; 0, 1, -1]

theorem primeZeroFrequencyMatrix_mulVec (a b c : R) :
    (primeZeroFrequencyMatrix m).mulVec ![a,b,c] = ![a + m*(b+c), a-c, b-c] := by
  funext i
  fin_cases i <;> simp [primeZeroFrequencyMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

theorem primeZeroFrequencyMatrix_det :
    (primeZeroFrequencyMatrix (R := R) m).det = 2*(m : R)+1 := by
  simp [primeZeroFrequencyMatrix, Matrix.det_fin_three]
  ring

theorem primeZeroFrequencyMatrix_isUnit (h : IsUnit (2*(m : R)+1)) :
    IsUnit (primeZeroFrequencyMatrix (R := R) m) := by
  rwa [Matrix.isUnit_iff_isUnit_det, primeZeroFrequencyMatrix_det]

/-- Recover the original three coordinates using just the inverse of the prime `2m+1`. -/
theorem primeZeroFrequencyMatrix_inv_mulVec (h : IsUnit (2*(m : R)+1)) (s x y : R) :
    ((primeZeroFrequencyMatrix (R := R) m)⁻¹).mulVec ![s,x,y] =
      let c := (↑(h.unit⁻¹) : R) * (s-x-m*y)
      ![x+c,y+c,c] := by
  let c := (↑(h.unit⁻¹) : R) * (s-x-m*y)
  have hc : (2*(m : R)+1)*c = s-x-m*y := by
    dsimp [c]
    rw [← mul_assoc, h.mul_val_inv, one_mul]
  apply Matrix.mulVec_injective_of_isUnit (primeZeroFrequencyMatrix_isUnit m h)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by simpa [primeZeroFrequencyMatrix_det] using h),
    Matrix.one_mulVec]
  change ![s,x,y] = (primeZeroFrequencyMatrix m).mulVec ![x+c,y+c,c]
  rw [primeZeroFrequencyMatrix_mulVec]
  have hs : s = x + c + m * (y + c + c) := by linear_combination -hc
  simp [hs]

/-- Four elementary row additions, one scaling by the prime, and cyclic reindexing
provide a uniform factorization of the constant-frequency block. -/
theorem primeZeroFrequencyMatrix_factor :
    primeZeroFrequencyMatrix (R := R) m =
      (Matrix.of fun i j : Fin 3 => if i+2 = j then (1 : R) else 0) *
        (Matrix.transvection 2 0 1 * (Matrix.transvection 2 1 (m : R) *
          (Matrix.diagonal ![1,1,(2*(m : R)+1)] *
            (Matrix.transvection 1 2 (-1) * Matrix.transvection 0 2 (-1))))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [primeZeroFrequencyMatrix, Matrix.transvection, Matrix.single_apply, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  ring

end ZeroFrequency

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
