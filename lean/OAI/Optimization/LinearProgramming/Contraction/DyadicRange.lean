import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding
import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-! ## Binary wire and logarithmic cost of the scalar threshold caller's power-of-two range -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contraction
open OracleSpec

/-- On this range the native PCG runtime charges precisely one more than the evaluation precision. -/
theorem nativeRange_log (b : ℕ) : (2^(b+1)+1:ℕ).log2 = b+1 := by
  have nz : 2^(b+1)+1 ≠ 0 := Nat.succ_ne_zero _
  have gap : 1 < (2:ℕ)^(b+1) := Nat.one_lt_two_pow (Nat.succ_ne_zero b)
  apply le_antisymm
  · apply Nat.le_of_lt_succ
    apply (Nat.log2_lt nz).mpr
    rw [Nat.pow_succ 2 (b+1)]
    omega
  · exact (Nat.le_log2 nz).mpr (Nat.le_succ _)

/-- Exact little-endian digits, including the high bit. -/
theorem nativePower_bits (k : ℕ) : ((2:ℕ)^k).bits = List.replicate k false ++ [true] := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ((2 : ℕ)^(k+1)).bits = (2 * 2^k).bits :=
        congrArg Nat.bits (Nat.pow_succ' (m := 2) (n := k))
      _ = false :: (2^k).bits := Nat.bit0_bits (2^k) (Nat.ne_of_gt (Nat.two_pow_pos k))
      _ = List.replicate (k+1) false ++ [true] := by
        rw [List.replicate_succ]
        exact congrArg (List.cons false) ih

private theorem frame_zeros (k : ℕ) : frame (List.replicate k false ++ [true]) =
    (List.replicate k ([true,false]:Word)).flatten ++ [true,true,false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ]
    change true::false::frame (List.replicate k false++[true]) =
      true::false::((List.replicate k ([true,false]:Word)).flatten ++ [true,true,false])
    rw [ih]

/-- An address counting precision can directly emit this range in `O(b)` bit writes. -/
theorem nativeRange_encode (b : ℕ) : encodeNat (2^(b+1)) =
    (List.replicate (b+1) ([true,false]:Word)).flatten ++ [true,true,false] := by
  rw [encodeNat,nativePower_bits,frame_zeros]

theorem nativeRange_encode_length (b : ℕ) : (encodeNat (2^(b+1))).length = 2*b+5 := by
  rw [encodeNat,OracleSpec.frame_length,nativePower_bits]
  simp only [List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

end Contraction
end LinearProgramming
end Optimization
end OAI
