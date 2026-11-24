import OAI.Computability.VPVNP.RankQueryStackField
import OAI.Computability.VPVNP.SliceArithmeticConstantEmit
import OAI.Computability.VPVNP.SliceArithmeticRound

/-!
# Power-basis representation of a signed coefficient

A matrix coefficient supplied as the difference of two nonnegative counts
reduces to one prime-field limb. Storing that limb followed by zero padding
writes exactly the scalar used by the determinant stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

open SliceArithmetic SliceArithmeticRound BurstRAM RAMTape

private theorem packed_zeros {p : ℕ} [NeZero p] (w n : ℕ) :
    packed w (List.replicate n (0 : Fin p)) = List.replicate (n * w) false := by
  induction n with
  | zero => simp [packed]
  | succ n ih =>
    rw [List.replicate_succ, packed, List.flatMap_cons]
    change wordBits (Word.limb w (0 : Fin p)) ++ packed w (List.replicate n (0 : Fin p)) = _
    rw [ih, Nat.succ_mul, Nat.add_comm, List.replicate_add, UnaryWord.zeros_wordBits w]
    simp [Word.limb]

/-- The packed constant vector has exactly the bit prefix returned by the
fixed constant emitter. -/
theorem packed_scale_one {p e : ℕ} [NeZero p] (he : 0 < e) (w : ℕ) (a : Fin p) :
    packed w (List.ofFn (scale a (one p e))) =
      wordBits (Word.limb w a) ++ List.replicate ((e - 1) * w) false := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [List.ofFn_succ]
  have htail : (fun i : Fin n => scale a (one p (n + 1)) i.succ) = fun _ => 0 := by
    funext i
    simp [scale, one]
  rw [htail, List.ofFn_const, packed, List.flatMap_cons]
  change wordBits (Word.limb w (scale a (one p (n+1)) 0)) ++
    packed w (List.replicate n (0 : Fin p)) = _
  simp [packed_zeros, scale, one]

namespace Scalar

/-- Reducing the two counts modulo the advised prime, subtracting them and
packing the result in the low limb realizes integer casting into the scalar ring. -/
theorem pack_signed_counts {p e : ℕ} [Fact p.Prime] [NeZero e]
    (c : Vector p e) (positive negative : ℕ) :
    pack c (scale (Fin.ofNat p positive - Fin.ofNat p negative) (one p e)) =
      (((positive : ℤ) - (negative : ℤ) : ℤ) : Scalar c) := by
  apply interpret_injective c
  change value (modulus c) (pack c (scale _ (one p e))).digits =
    interpretation c (((positive : ℤ) - (negative : ℤ) : ℤ) : Scalar c)
  rw [digits_pack, value_scale, value_one, mul_one, map_intCast]
  have h (n : ℕ) : ZMod.finEquiv p (Fin.ofNat p n) = (n : ZMod p) := by
    rw [← cast_val_eq_finEquiv, Fin.val_ofNat, ZMod.natCast_mod]
  simp only [cast_val_eq_finEquiv, map_sub, h, map_natCast, Int.cast_sub, Int.cast_natCast]

end Scalar

end RankQuery.Stack

end VPVNP
end Computability
end OAI
