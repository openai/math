import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Quaternion arithmetic for the congruence covers

Section 5.1 of *An explicit VNP family requires superpolynomial border circuit size
over every field* uses the order with generators `i² = 2`, `j² = 3`, `ij = -ji`.
Its reduced norm is anisotropic over the integers by descent at the prime three.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- The integral quaternion order used for tile addresses. -/
abbrev Order := QuaternionAlgebra ℤ 2 0 3

/-- The reduced norm of the quaternion order, equal to the determinant in its real split model. -/
def norm (x : Order) : ℤ := x.re ^ 2 - 2 * x.imI ^ 2 - 3 * x.imJ ^ 2 + 6 * x.imK ^ 2

/-- Reduced norm respects multiplication, including noncommuting arguments. -/
theorem norm_mul (x y : Order) : norm (x * y) = norm x * norm y := by
  rcases x with ⟨a, b, c, d⟩
  rcases y with ⟨e, f, g, h⟩
  simp only [norm, QuaternionAlgebra.mk_mul_mk]
  ring

private theorem three_dvd_pair {a b t : ℤ} (h : a ^ 2 - 2 * b ^ 2 = 3 * t) :
    3 ∣ a ∧ 3 ∣ b := by
  have modEq := congrArg (fun z : ℤ => (z : ZMod 3)) h
  push_cast at modEq
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [h3, zero_mul] at modEq
  have test : ∀ (x y : ZMod 3), x ^ 2 - 2 * y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := test _ _ modEq
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 ha,
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hb⟩

private theorem descend {a b c d : ℤ}
    (h : a ^ 2 - 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 = 0) :
    ∃ a' b' c' d' : ℤ, a = 3 * a' ∧ b = 3 * b' ∧ c = 3 * c' ∧ d = 3 * d' ∧
      a' ^ 2 - 2 * b' ^ 2 - 3 * c' ^ 2 + 6 * d' ^ 2 = 0 := by
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ :=
    three_dvd_pair (a := a) (b := b) (t := c ^ 2 - 2 * d ^ 2) (by linarith)
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ :=
    three_dvd_pair (a := c) (b := d) (t := a' ^ 2 - 2 * b' ^ 2) (by linarith)
  exact ⟨_, _, _, _, rfl, rfl, rfl, rfl, by linarith⟩

/-- Every integral quaternion with vanishing norm vanishes. -/
theorem eq_zero_of_norm_eq_zero (x : Order) (h : norm x = 0) : x = 0 := by
  rcases x with ⟨a, b, c, d⟩
  change a ^ 2 - 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 = 0 at h
  generalize hm : a.natAbs + b.natAbs + c.natAbs + d.natAbs = m
  induction m using Nat.strong_induction_on generalizing a b c d with
  | h m ih =>
    obtain ⟨a', b', c', d', rfl, rfl, rfl, rfl, hh⟩ := descend h
    simp only [Int.natAbs_mul, show (3 : ℤ).natAbs = 3 by decide] at hm
    by_cases zero : a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs = 0
    · have : a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0 := by
        simpa only [Nat.add_eq_zero_iff, Int.natAbs_eq_zero, and_assoc] using zero
      obtain ⟨rfl, rfl, rfl, rfl⟩ := this
      rfl
    · have smaller := ih _ (show a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs < m by omega)
          a' b' c' d' hh rfl
      change (QuaternionAlgebra.mk a' b' c' d' : Order) = ⟨0, 0, 0, 0⟩ at smaller
      cases smaller
      rfl

/-- The scalar leading coefficient in a positive-depth norm-one layer is zero mod seven. -/
theorem leading_scalar_dvd (l : ℕ) (x : Order) (h : norm (1 + (7 : ℤ) ^ (l+1) • x) = 1) :
    7 ∣ x.re := by
  let s : ℤ := 7 ^ l
  have hs : s ≠ 0 := pow_ne_zero l (by decide : (7 : ℤ) ≠ 0)
  have hn : 7*s * (2*x.re + 7*s * norm x) = 0 := by
    rcases x with ⟨a,b,c,d⟩
    simp only [norm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
      QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add,
      QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one,
      QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one,
      QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul, pow_succ] at h
    dsimp [s, norm]
    linarith
  have eqn := (mul_eq_zero.mp hn).resolve_left (mul_ne_zero (by decide) hs)
  have : 2 * x.re = -(7 * (s * norm x)) := by linarith
  omega

/-- First imaginary generator of the integral order. -/
def basisI : Order := ⟨0, 1, 0, 0⟩
/-- The second generating direction of the integral order. -/
def basisJ : Order := ⟨0, 0, 1, 0⟩
/-- The product of the two generating directions. -/
def basisK : Order := ⟨0, 0, 0, 1⟩

/-- The bracket constants of Lemma 5.1 are invertible modulo seven. -/
theorem basis_brackets :
    basisI * basisJ - basisJ * basisI = (2 : ℤ) • basisK ∧
    basisJ * basisK - basisK * basisJ = (-6 : ℤ) • basisI ∧
    basisK * basisI - basisI * basisK = (-4 : ℤ) • basisJ := by
  exact ⟨rfl, rfl, rfl⟩

/-- The two norm-one elements at depth one used to start the congruence tower. -/
theorem depth_one_generators :
    (3 + 2*basisI)^3 = (⟨99,70,0,0⟩ : Order) ∧
    (2 + basisJ)^8 = (⟨18817,0,10864,0⟩ : Order) ∧
    norm (3 + 2*basisI) = 1 ∧ norm (2 + basisJ) = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Cover

end BorderVNP
end Computability
end OAI
