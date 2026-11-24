import OAI.Computability.VPVNP.SliceArithmeticMul
import Mathlib.Data.Nat.Size

/-!
# Powers and inverses in the evaluator's finite slice field

Each instruction in the binary powering routine is one multiplication of
coefficient vectors. The inverse routine handles zero separately, including
the case of a field of order two where the Fermat exponent is zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic

/-- An instruction takes the running product and either squares it or
multiplies it by the original base. -/
inductive PowerStep where
  | square
  | multiplyBase
  deriving DecidableEq

/-- Read the binary exponent from its most significant bit. -/
def powerSteps (n : ℕ) : List PowerStep :=
  n.bits.reverse.flatMap fun bit =>
    if bit then [.square, .multiplyBase] else [.square]

private theorem powerSteps_bit (n : ℕ) (b : Bool) (h : n = 0 → b = true) :
    powerSteps (Nat.bit b n) =
      powerSteps n ++ (if b then [.square, .multiplyBase] else [.square]) := by
  simp [powerSteps, Nat.bits_append_bit n b h]

/-- The exact number of vector multiplications is the bit length plus the
number of one bits. -/
theorem powerSteps_length (n : ℕ) :
    (powerSteps n).length = n.size + n.bits.count true := by
  induction n using Nat.binaryRec' with
  | zero => simp [powerSteps]
  | bit b n h ih =>
    rw [powerSteps_bit n b h, List.length_append, ih, Nat.bits_append_bit n b h,
      Nat.size_bit (Nat.bit_ne_zero_iff.mpr h)]
    cases b <;> simp <;> omega

theorem powerSteps_length_le (n : ℕ) : (powerSteps n).length ≤ 2 * n.size := by
  rw [powerSteps_length]
  have h := List.count_le_length (a := true) (l := n.bits)
  rw [Nat.size_eq_bits_len] at h
  omega

variable {p e : ℕ} [NeZero p]

/-- Execute one binary powering instruction by squaring the accumulator or multiplying it by
the saved base modulo the defining polynomial. -/
def PowerStep.run (c base acc : Vector p e) : PowerStep → Vector p e
  | .square => mul c acc acc
  | .multiplyBase => mul c acc base

/-- Execute the binary powering program with initial value one. -/
def pow (c base : Vector p e) (n : ℕ) : Vector p e :=
  (powerSteps n).foldl (PowerStep.run c base) (one p e)

theorem value_pow [NeZero e] (c base : Vector p e) (n : ℕ) :
    value (modulus c) (pow c base n) = value (modulus c) base ^ n := by
  induction n using Nat.binaryRec' with
  | zero => simp [pow, powerSteps]
  | bit b n h ih =>
    unfold pow at ih ⊢
    rw [powerSteps_bit n b h, List.foldl_append]
    cases b <;> simp [PowerStep.run, value_mul, ih, Nat.bit, pow_add, pow_mul, sq, mul_comm 2 n]

/-- Zero gets the zero vector. A nonzero input uses the Fermat exponent. -/
def inverse (c a : Vector p e) : Vector p e :=
  if a = zero p e then zero p e else pow c a (p ^ e - 2)

/-- The instructions executed for the input-dependent inverse routine. -/
def inverseSteps (a : Vector p e) : List PowerStep :=
  if a = zero p e then [] else powerSteps (p ^ e - 2)

theorem inverse_eq_fold (c a : Vector p e) :
    inverse c a = (inverseSteps a).foldl (PowerStep.run c a)
      (if a = zero p e then zero p e else one p e) := by
  by_cases h : a = zero p e <;> simp [inverse, inverseSteps, pow, h]

theorem inverseSteps_length_le (a : Vector p e) :
    (inverseSteps a).length ≤ 2 * (e * Nat.clog 2 p) := by
  unfold inverseSteps
  split
  · simp
  · apply (powerSteps_length_le _).trans
    apply Nat.mul_le_mul_left
    apply Nat.size_le.mpr
    calc
      p ^ e - 2 < p ^ e := by have := Nat.pow_pos (NeZero.pos p) (n := e); omega
      _ ≤ (2 ^ Nat.clog 2 p) ^ e := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
      _ = 2 ^ (e * Nat.clog 2 p) := by rw [← pow_mul, Nat.mul_comm]

section Field

variable {q : ℕ} [Fact q.Prime]

/-- A monic presentation of degree `e` over the prime field has `q ^ e` elements. -/
theorem adjoinRoot_card (c : Vector q e) : Nat.card (AdjoinRoot (modulus c)) = q ^ e := by
  let b := (AdjoinRoot.powerBasis' (modulus_monic c)).basis
  let := Fintype.ofEquiv _ b.equivFun.toEquiv.symm
  rw [Nat.card_eq_fintype_card, Module.card_fintype b, ZMod.card]
  change q ^ Fintype.card (Fin (modulus c).natDegree) = _
  rw [Fintype.card_fin, modulus_natDegree]

theorem value_inverse [NeZero e] (c a : Vector q e) [Fact (Irreducible (modulus c))] :
    value (modulus c) (inverse c a) = (value (modulus c) a)⁻¹ := by
  unfold inverse
  split
  next h => simp [h]
  next h =>
    have ha : value (modulus c) a ≠ 0 := by
      intro hz
      exact h (value_injective (modulus_monic c) (modulus_natDegree c) (hz.trans (value_zero _).symm))
    rw [value_pow]
    apply eq_inv_of_mul_eq_one_left
    let b := (AdjoinRoot.powerBasis' (modulus_monic c)).basis
    let := Fintype.ofEquiv _ b.equivFun.toEquiv.symm
    have hq : 1 < q ^ e := one_lt_pow₀ (Fact.out : q.Prime).one_lt (NeZero.ne e)
    have hcard : Fintype.card (AdjoinRoot (modulus c)) = q ^ e :=
      Nat.card_eq_fintype_card.symm.trans (adjoinRoot_card c)
    rw [← pow_succ, show q ^ e - 2 + 1 = q ^ e - 1 by omega, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one _ ha

end Field
end SliceArithmetic

end VPVNP
end Computability
end OAI
