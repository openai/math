import OAI.Computability.BorderVNP.ResidueJetChange
import OAI.Computability.BorderVNP.ResidueLaurentDerivative
import Mathlib.RingTheory.AdjoinRoot

/-!
# Truncated jets in a branch parameter

The top coefficient of the quotient by `U^p` reads the one-variable Cartier
operator. Replacing `U` by the increment of another Laurent parameter and
multiplying by its differential changes this functional by its Frobenius
Jacobian. This applies to ramified parameters whenever their derivative is
nonzero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue.BranchJet

open Polynomial
open scoped LaurentSeries

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The univariate truncated jet algebra at the branch. -/
abbrev Ring (K : Type*) [Field K] (p : ℕ) := AdjoinRoot ((X : (LaurentSeries K)[X]) ^ p)

private noncomputable abbrev modulus := (X : (LaurentSeries K)[X]) ^ p

/-- The nilpotent increment of the branch uniformizer. -/
noncomputable def increment : Ring K p := AdjoinRoot.root (modulus p)

omit [Fact p.Prime] [CharP K p] [PerfectRing K p] in
/-- The defining power of the increment vanishes. -/
theorem increment_pow : (increment (K := K) p) ^ p = 0 := by
  rw [increment, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_eq_zero]

omit [CharP K p] [PerfectRing K p] in
private theorem of_injective : Function.Injective (AdjoinRoot.of (modulus (K := K) p)) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos (monic_X_pow _) (by
    rw [degree_X_pow]; exact_mod_cast (Fact.out : p.Prime).pos)

/-- The Laurent completion has the characteristic of its coefficient field. -/
scoped instance laurentChar : CharP (LaurentSeries K) p :=
  charP_of_injective_ringHom HahnSeries.C_injective p

/-- Truncation of the positive-order jet preserves the characteristic. -/
scoped instance jetChar : CharP (Ring K p) p :=
  charP_of_injective_ringHom (of_injective p) p

/-- Taylor substitution at the nilpotent increment of the uniformizer. -/
noncomputable def jet : LaurentSeries K →+* Ring K p :=
  taylorJet p 1 (AdjoinRoot.of (modulus p)) (increment p) (by simpa using increment_pow (K := K) p)

omit [Fact p.Prime] [CharP K p] [PerfectRing K p] in
/-- Coefficient of degree `p−1` on the quotient. -/
noncomputable def top : Ring K p →ₗ[LaurentSeries K] LaurentSeries K :=
  (Polynomial.lcoeff _ (p-1)).comp (AdjoinRoot.modByMonicHom (monic_X_pow _))

omit [CharP K p] [PerfectRing K p] in
/-- Multiples of the truncating monomial have zero top coefficient. -/
theorem top_mk (f : (LaurentSeries K)[X]) :
    top p (AdjoinRoot.mk (modulus p) f) = f.coeff (p-1) := by
  change (f %ₘ (X ^ p)).coeff (p-1) = _
  rw [modByMonic_eq_sub_mul_div, coeff_sub, coeff_X_pow_mul', ite_eq_right, sub_zero]
  have := (Fact.out : p.Prime).pos
  omega

/-- The jet equals the class of its Taylor polynomial representative. -/
theorem jet_eq_mk (D : LaurentSeries K) :
    jet p D = AdjoinRoot.mk (modulus p) (jetPolynomial p 1 D) := by
  rw [jet, ← eval_jetPolynomial, ← AdjoinRoot.aeval_eq, aeval_def]
  rfl

/-- Taking the top coefficient of a branch Taylor jet is Frobenius of Cartier. -/
theorem top_jet (D : LaurentSeries K) : top p (jet p D) = cartier p 1 D ^ p := by
  rw [jet_eq_mk, top_mk]
  simpa using jetPolynomial_top_coeff p 1 D

/-- Taylor substitution fixes Frobenius powers of Laurent functions. -/
theorem jet_pow (D : LaurentSeries K) :
    jet p (D ^ p) = algebraMap (LaurentSeries K) (Ring K p) (D ^ p) := by
  unfold jet taylorJet
  simpa using jetHom_term p 1 (AdjoinRoot.of (modulus (K := K) p))
    ((AdjoinRoot.of (modulus p)) (parameter K) + increment p)
    (by rw [pow_one, add_pow_char, increment_pow, add_zero, map_pow]) 0 D

/-- Taylor substitution fixes every element from a perfect coefficient field. -/
theorem jet_comp_of_perfect {E : Type*} [Field E] [ExpChar E p] [PerfectRing E p]
    (φ : E →+* LaurentSeries K) :
    (jet p).comp φ = (algebraMap _ (Ring K p)).comp φ := by
  ext c
  obtain ⟨b, hb⟩ := surjective_frobenius E p c
  change b ^ p = c at hb
  rw [← hb]
  simp only [RingHom.comp_apply, map_pow]
  exact (map_pow (jet p) (φ b) p).symm.trans ((jet_pow p (φ b)).trans (map_pow _ _ _))

/-- The Frobenius power of the Jacobian can leave the branch jet before taking
the top coefficient. This is the scalar manipulation in the chart formula. -/
theorem jacobian_weight (J A t' : LaurentSeries K) (hJ : J ≠ 0) :
    (t'^p)⁻¹ * top p (jet p (J^(p-1)) * jet p A * jet p t') =
      ((J / t') * cartier p 1 (A * (t'/J)))^p := by
  have hpow : J ^ p = J ^ (p-1) * J := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).pos]
  have h : J ^ (p-1) * A * t' = J ^ p * (A * (t'/J)) := by
    rw [hpow]
    field_simp
  rw [← map_mul, ← map_mul, h, map_mul, jet_pow, ← Algebra.smul_def, map_smul,
    smul_eq_mul, top_jet, mul_pow, div_pow, div_eq_mul_inv]
  ring

/-- The increment of any Laurent function is killed by the same Frobenius power. -/
theorem jet_sub_pow (D : LaurentSeries K) :
    (jet p D - algebraMap _ (Ring K p) D)^p = 0 := by
  rw [sub_pow_char, ← map_pow, ← map_pow, jet_pow, sub_self]

/-- A change of parameter on the differential jet scales the top coefficient by
the Frobenius of the new parameter's derivative. -/
theorem top_increment_derivative (t : LaurentSeries K) (r : ℕ) :
    top p ((jet p t - algebraMap _ (Ring K p) t)^r *
      jet p (LaurentSeries.derivative K t)) =
    if r = p - 1 then (LaurentSeries.derivative K t)^p else 0 := by
  let T := jetPolynomial p 1 t - C t
  have hzero : T.coeff 0 = 0 := by
    have h := eval_jetPolynomial p 1 (RingHom.id (LaurentSeries K)) 0
      (by simp [zero_pow (Fact.out : p.Prime).ne_zero]) t
    rw [taylorJet_zero] at h
    change (jetPolynomial p 1 t - C t).coeff 0 = 0
    rw [coeff_sub, coeff_C_zero, sub_eq_zero, coeff_zero_eq_eval_zero]
    exact h
  have hone : T.coeff 1 = LaurentSeries.derivative K t := by
    change (jetPolynomial p 1 t - C t).coeff 1 = _
    rw [coeff_sub, coeff_C, ite_eq_right (by decide), sub_zero, jetPolynomial_coeff_one p 1 (by decide)]
  have hj : jet p t - algebraMap _ (Ring K p) t = AdjoinRoot.mk (modulus p) T := by
    dsimp only [T]
    rw [jet_eq_mk, map_sub, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have hder : jet p (LaurentSeries.derivative K t) = AdjoinRoot.mk (modulus p) T.derivative := by
    rw [jet, ← eval_jetPolynomial_derivative p 1 (by decide), ← AdjoinRoot.aeval_eq, aeval_def]
    simp [T, AdjoinRoot.algebraMap_eq, increment]
  rw [hj, hder, ← map_pow, ← map_mul, top_mk]
  have h := top_jet_change p ((X : (LaurentSeries K)[X]) ^ r) T hzero
  simpa [hone, coeff_X_pow, ite_mul, eq_comm] using h

end Residue.BranchJet

end BorderVNP
end Computability
end OAI
