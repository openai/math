import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Optimization.LinearProgramming.Lattice.NativeNearestPublic

/-! The exact integer nearest quotient returned by the native LLL size reduction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal

/-- The integer nearest quotient is within a half of the real quotient, for both signs
and including ties. -/
theorem native_nearest_error (a : ℤ) (d : ℕ) (hd : 0 < d) :
    |(a : ℝ) / d - (LLLState.nearestQuotient a d : ℝ)| ≤ 1 / 2 := by
  let r := LLLState.nearestQuotient a d
  have hZ : 2 * |a - r * (d : ℤ)| ≤ (d : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast native_nearest_residue a d hd
  have hr : 2 * |(a : ℝ) - (r : ℝ) * (d : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hZ
  have hp : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [show (a : ℝ) / d - (LLLState.nearestQuotient a d : ℝ) =
      ((a : ℝ) - (r : ℝ) * d) / d from by dsimp [r]; field_simp, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  linarith

/-- The current valid state supplies the exact rational Gram coefficient represented
by a scaled integer entry and the next Gram determinant. -/
theorem native_stored_coefficient {n m : ℕ} (s : LLLState (n+1) m) (hs : s.Valid)
    {j k : Fin (n+1)} (hjk : j < k) :
    (((s.ν.getRow k).get j : ℤ) : ℝ) =
      (s.d.get j.succ : ℝ) * gsCoeff (Hex.GramSchmidtMathlib.intRowFamily s.b) k j := by
  let a := (s.ν.getRow k).get j
  let d := s.d.get j.succ
  have hrat : (a : ℚ) = (d : ℚ) * (Hex.GramSchmidt.Int.coeffs s.b)[k][j] := by
    change (((s.ν.getRow k).get j : ℤ) : ℚ) = _
    rw [hs.ν_eq k.val j.val k.isLt j.isLt hjk]
    rw [show d = Hex.GramSchmidt.Int.gramDet s.b (j.val+1) j.isLt from hs.d_eq _ _]
    exact Hex.GramSchmidt.Int.scaledCoeffs_eq s.b k.val j.val k.isLt hjk
  have h := congrArg (fun q : ℚ => (q : ℝ)) hrat
  push_cast at h
  rw [nativeCoeff_eq s.b hjk] at h
  exact h

end Lattice
end LinearProgramming
end Optimization
end OAI
