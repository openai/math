import OAI.Computability.VPVNP.SliceArithmetic

/-!
# Multiplication in the advised polynomial basis

A companion operation multiplies by the adjoined root in the quotient by the
advised monic polynomial. Horner's rule multiplies two coefficient vectors
using exactly one round for each coefficient of the first input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic

open Polynomial

variable {p e : ℕ} [NeZero p]

/-- The companion operation shifts the coordinates up one degree and uses the
advised monic relation to reduce the top coordinate. -/
def companion {p : ℕ} [NeZero p] : {e : ℕ} → Vector p e → Vector p e → Vector p e
  | 0, _, v => v
  | d + 1, c, v =>
      add (Fin.cons 0 (fun i : Fin d => v i.castSucc)) (scale (-v (Fin.last d)) c)

omit [NeZero p] in
theorem root_pow_modulus (c : Vector p e) :
    AdjoinRoot.root (modulus c) ^ e = -value (modulus c) c := by
  apply eq_neg_of_add_eq_zero_left
  have h := AdjoinRoot.mk_self (f := modulus c)
  change AdjoinRoot.mk (modulus c) (X ^ e + ∑ i, C ((c i).val : ZMod p) * X ^ i.val) = 0 at h
  simpa [value, AdjoinRoot.algebraMap_eq] using h

theorem value_companion (c v : Vector p e) :
    value (modulus c) (companion c v) = AdjoinRoot.root (modulus c) * value (modulus c) v := by
  cases e with
  | zero => simp [value]
  | succ d =>
    let f := modulus c
    let r := AdjoinRoot.root f
    let A := algebraMap (ZMod p) (AdjoinRoot f)
    have hshift :
        value f (Fin.cons 0 (fun i : Fin d => v i.castSucc)) =
        r * ∑ i : Fin d, A ((v i.castSucc).val : ZMod p) * r ^ i.val := by
      rw [value, Fin.sum_univ_succ, Finset.mul_sum]
      simp [Fin.cons, A, r, pow_succ, mul_assoc, mul_comm]
    have hsplit : value f v =
        (∑ i : Fin d, A ((v i.castSucc).val : ZMod p) * r ^ i.val) +
          A ((v (Fin.last d)).val : ZMod p) * r ^ d :=
      Fin.sum_univ_castSucc _
    change value f (add _ _) = r * value f v
    rw [value_add, value_scale, hshift, hsplit, cast_val_eq_finEquiv (-v _), map_neg,
      ← cast_val_eq_finEquiv, map_neg, mul_add]
    have hpow : r ^ (d + 1) = -value f c := root_pow_modulus c
    rw [← neg_eq_iff_eq_neg.mpr hpow]
    ring

/-- Horner's rule traverses the coefficients from highest to lowest, using
one companion operation, one scalar multiplication and one addition per round. -/
def horner (c b : Vector p e) (coefficients : List (Fin p)) : Vector p e :=
  coefficients.foldr (fun a acc => add (companion c acc) (scale a b)) (zero p e)

/-- Multiplication modulo the advised monic polynomial. -/
def mul (c a b : Vector p e) : Vector p e := horner c b (List.ofFn a)

omit [NeZero p] in
theorem horner_rounds (a : Vector p e) : (List.ofFn a).length = e := List.length_ofFn

theorem value_horner (c b : Vector p e) {k : ℕ} (a : Vector p k) :
    value (modulus c) (horner c b (List.ofFn a)) =
      value (modulus c) a * value (modulus c) b := by
  induction k with
  | zero =>
    rw [List.ofFn_zero, horner, List.foldr_nil, value_zero]
    simp [value]
  | succ k ih =>
    rw [List.ofFn_succ]
    change value _ (add (companion c (horner c b _)) (scale _ b)) = _
    rw [value_add, value_companion, value_scale, ih]
    have htail : value (modulus c) a =
        algebraMap (ZMod p) _ ((a 0).val : ZMod p) +
          AdjoinRoot.root (modulus c) * value (modulus c) (fun i : Fin k => a i.succ) := by
      unfold value
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp [pow_succ, mul_assoc, mul_comm]
    rw [htail]
    ring

theorem value_mul (c a b : Vector p e) :
    value (modulus c) (mul c a b) = value (modulus c) a * value (modulus c) b :=
  value_horner c b a

end SliceArithmetic

end VPVNP
end Computability
end OAI
