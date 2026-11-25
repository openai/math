import OAI.Hierarchy.DescentIrreducibleSearch
import Mathlib.Data.List.ProdSigma
import Mathlib.RingTheory.AdjoinRoot

namespace OAI
/-! # Bounded multiplication in a binary polynomial residue ring

The executable search compares the coefficients of two products through degree
`2*k`. Its query pairs range over all `k`-bit quotients and remainders. A monic
divisor gives a successful comparison, and evaluation in its quotient proves the
result is the power-basis product. An irreducible candidate therefore supplies the
multipliers of the finite-field layout.
-/

namespace Hierarchy.DescentBinaryField
open Polynomial DescentGL
open scoped Polynomial BigOperators

variable {k : ℕ}

/-- Coordinates in the basis of successive powers of the residue class of `X`. -/
noncomputable def residueCoordinates (a : Bits k) :
    AdjoinRoot (candidate a) ≃ₗ[ZMod 2] Bits k :=
  (AdjoinRoot.powerBasisAux' (candidate_monic a)).equivFun.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr (candidate_degree a).symm))

theorem residueCoordinates_symm (a x : Bits k) :
    (residueCoordinates a).symm x = AdjoinRoot.mk (candidate a) (wordPolynomial x) := by
  apply (residueCoordinates a).injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  change x i = (AdjoinRoot.modByMonicHom (candidate_monic a)
    (AdjoinRoot.mk (candidate a) (wordPolynomial x))).coeff i.val
  have below : (wordPolynomial x).degree < (candidate a).degree := by
    rw [degree_eq_natDegree (candidate_monic a).ne_zero, candidate_degree]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast wordPolynomial_degree_lt (Nat.zero_lt_of_lt i.isLt) x)
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff (candidate_monic a)).mpr below,
    wordPolynomial_coeff]
  simp [bitAt,i.isLt]

/-- Bit test for `x*y = remainder + modulus*quotient`. -/
def productTest (a x y : Bits k) (pair : Bits k × Bits k) : Bool :=
  agreeBelow k (convolution (bitAt x) (bitAt y)) (fun n =>
    bitAt pair.2 n + convolution (candidateBit a) (bitAt pair.1) n)

theorem productTest_iff (a x y u v : Bits k) :
    productTest a x y (u,v) = true ↔
      wordPolynomial x * wordPolynomial y = wordPolynomial v + candidate a * wordPolynomial u := by
  have left : convolution (bitAt x) (bitAt y) = (wordPolynomial x * wordPolynomial y).coeff := by
    rw [← funext (wordPolynomial_coeff x), ← funext (wordPolynomial_coeff y)]
    exact funext (convolution_coeff _ _)
  have right : (fun n => bitAt v n + convolution (candidateBit a) (bitAt u) n) =
      (wordPolynomial v + candidate a * wordPolynomial u).coeff := by
    rw [← funext (wordPolynomial_coeff v), ← funext (wordPolynomial_coeff u), ← funext (candidate_coeff a)]
    funext n
    rw [coeff_add,convolution_coeff]
  have lm : (wordPolynomial x * wordPolynomial y).natDegree ≤ 2*k :=
    (natDegree_mul_le_of_le (wordPolynomial_degree_le x) (wordPolynomial_degree_le y)).trans (by omega)
  have rm : (candidate a * wordPolynomial u).natDegree ≤ 2*k :=
    (natDegree_mul_le_of_le (candidate_degree a).le (wordPolynomial_degree_le u)).trans (by omega)
  simpa only [productTest, left, right] using
    (agreeBelow_poly_iff (wordPolynomial x * wordPolynomial y)
      (wordPolynomial v + candidate a * wordPolynomial u) lm
      (natDegree_add_le_of_degree_le ((wordPolynomial_degree_le v).trans (by omega)) rm))

private theorem exists_pair (hk : 0<k) (a x y : Bits k) :
    ∃ u v, productTest a x y (u,v) = true := by
  let p := wordPolynomial x * wordPolynomial y
  let f := candidate a
  have small : p.natDegree < 2*k := by
    have h : p.natDegree ≤ (wordPolynomial x).natDegree + (wordPolynomial y).natDegree := natDegree_mul_le
    have hx := wordPolynomial_degree_lt hk x
    have hy := wordPolynomial_degree_lt hk y
    omega
  have monic : f.Monic := candidate_monic a
  have degree : f.natDegree=k := candidate_degree a
  have nonunit : f≠1 := by
    intro eqn
    rw [eqn,natDegree_one] at degree
    omega
  have div : (p /ₘ f).natDegree < k := by rw [natDegree_divByMonic p monic, degree]; omega
  have rem : (p %ₘ f).natDegree < k := degree ▸ natDegree_modByMonic_lt p monic nonunit
  refine ⟨fun i => (p /ₘ f).coeff i.val, fun i => (p %ₘ f).coeff i.val, (productTest_iff ..).mpr ?_⟩
  rw [wordPolynomial_of_coeff _ div, wordPolynomial_of_coeff _ rem]
  exact (modByMonic_add_div p f).symm

/-- Count the bit operations through the first unequal coefficient. At coefficient
`n` the two convolutions require two products and two sums per tap. The leading-bit
correction requires one additional sum per tap, followed by one remainder addition
and one comparison. -/
def measuredResidueTest (a x y : Bits k) (pair : Bits k × Bits k) : Bool × ℕ :=
  allWithCost (fun n =>
    (decide (convolution (bitAt x) (bitAt y) n =
      bitAt pair.2 n + convolution (candidateBit a) (bitAt pair.1) n), 5*(n+1)+2))
    (List.range (2*k+1))

theorem measuredResidueTest_read (a x y : Bits k) (pair : Bits k × Bits k) :
    (measuredResidueTest a x y pair).1 = productTest a x y pair :=
  allWithCost_read _ _

theorem measuredResidueTest_work (a x y : Bits k) (pair : Bits k × Bits k) :
    (measuredResidueTest a x y pair).2 ≤ (2*k+1)*(5*(2*k+1)+2) := by
  unfold measuredResidueTest
  apply (allWithCost_bound _ _ (5*(2*k+1)+2) ?_).trans_eq (by rw [List.length_range])
  intro n hn
  have := List.mem_range.mp hn
  dsimp
  omega

/-- Test concrete little-endian pairs through the first success, retaining the
actual coefficient-comparison work. -/
def multiplyRun (a x y : Bits k) := findWithCost (measuredResidueTest a x y) ((words k) ×ˢ (words k))

private theorem multiplyRun_value (a x y : Bits k) :
    (multiplyRun a x y).1 = ((words k) ×ˢ (words k)).find? (productTest a x y) := by
  simp only [multiplyRun, findWithCost_read, measuredResidueTest_read]

def multiply (a x y : Bits k) : Bits k := ((multiplyRun a x y).1.map Prod.snd).getD 0

theorem multiply_correct (hk : 0<k) (a x y : Bits k) :
    multiply a x y = residueCoordinates a ((residueCoordinates a).symm x * (residueCoordinates a).symm y) := by
  obtain ⟨u,v,good⟩ := exists_pair hk a x y
  have found := multiplyRun_value a x y
  cases eqn : (multiplyRun a x y).1 with
  | none =>
    rw [eqn] at found
    have never := List.find?_eq_none.mp found.symm (u,v) (by simp)
    exact (never good).elim
  | some pair =>
    rw [eqn] at found
    have eqprod := (productTest_iff a x y pair.1 pair.2).mp (List.find?_some found.symm)
    have images := congrArg (AdjoinRoot.mk (candidate a)) eqprod
    simp only [map_add,map_mul,AdjoinRoot.mk_self,zero_mul,add_zero] at images
    apply (residueCoordinates a).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    simpa only [multiply, eqn, Option.map_some, Option.getD_some, residueCoordinates_symm] using images.symm

/-- The total charged bit operations are at most a quadratic polynomial in `k`
times the `(2^k)^2` possible quotient–remainder pairs. -/
theorem multiplyRun_work (a x y : Bits k) :
    (multiplyRun a x y).2 ≤ (2^k)^2*((2*k+1)*(5*(2*k+1)+2)) := by
  unfold multiplyRun
  apply (findWithCost_bound _ _ ((2*k+1)*(5*(2*k+1)+2))
    (fun pair _ => measuredResidueTest_work a x y pair)).trans_eq
  rw [List.length_product, length_words, pow_two]


end Hierarchy.DescentBinaryField

end OAI
