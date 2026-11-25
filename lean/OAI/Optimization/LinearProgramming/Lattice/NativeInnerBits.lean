import OAI.Optimization.LinearProgramming.Lattice.NativeColumnValidity
import OAI.Optimization.LinearProgramming.Lattice.NativeColumnHeight
import OAI.Optimization.LinearProgramming.Lattice.LLLColumnTrace
import OAI.Optimization.LinearProgramming.Lattice.NativeStoredBits
import OAI.Optimization.LinearProgramming.Lattice.NativePassFrame

/-! Bit heights at every visited column of the native inner loop, including the
intermediate basis rows before the full pass is reduced. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Hex.Internal
open Hex.GramSchmidtMathlib (intRowFamily)

private theorem column_growth_factor (H : ℕ) :
    1 + ((2 : ℝ)^H+1)*(2:ℝ)^H ≤ (2:ℝ)^(2*H+2) := by
  have h : 1 ≤ (2:ℝ)^H := one_le_pow₀ (by norm_num)
  rw [pow_add (2:ℝ) (2*H) 2, two_mul H, pow_add]
  nlinarith [sq_nonneg ((2:ℝ)^H-1)]

/-- From bounded pass input and Gram table, every concrete state in the native
right-to-left column trace has polynomially bounded stored basis and coefficient bits. -/
theorem native_pass_basis_bits {n m H : ℕ} (s : LLLState (n+1) m)
    (hs : s.Valid) (hind : s.b.independent) (hD : ∀ a, s.d.get a ≤ 2^H)
    (hrow : ∀ i, ‖intRowFamily s.b i‖ + 1 ≤ (2:ℝ)^H) (k : Fin (n+1))
    {t : LLLState (n+1) m} (ht : IsPassState s k t) (i : Fin (n+1)) (l : Fin m) :
    (t.b[i][l]).natAbs.size ≤ (2*H+2)*n+H := by
  let P (j : ℕ) (t : LLLState (n+1) m) :=
    t.Valid ∧ t.b.independent ∧ t.d = s.d ∧
    (∀ i ≠ k, intRowFamily t.b i = intRowFamily s.b i) ∧
      ‖intRowFamily t.b k‖ + 1 ≤ (2:ℝ)^((2*H+2)*j+H)
  have hbase : P 0 s := ⟨hs, hind, rfl, fun _ _ => rfl, by simpa using hrow k⟩
  have hstep a (t : LLLState (n+1) m) j (hj : j < k) (ht : P a t) :
      P (a+1) (t.sizeReduceColumn j k hj) := by
    obtain ⟨htv, hti, htd, hother, hnorm⟩ := ht
    refine ⟨LLLState.sizeReduceColumn_valid t j k hj htv, native_column_independent t j k hj hti,
      (native_column_gram_table t j k hj).trans htd, ?_, ?_⟩
    · exact fun i hi => (native_column_other_row t j k i hj hi).trans (hother i hi)
    · have hd : ∀ x, t.d.get x ≤ 2^H := by simpa only [htd] using hD
      have hb : ‖intRowFamily t.b j‖ ≤ (2:ℝ)^H := by
        rw [hother j hj.ne]
        linarith [hrow j]
      have h := native_column_height t htv hti hd hj hb
      push_cast at h
      calc
        _ ≤ (1 + ((2:ℝ)^H+1)*(2:ℝ)^H) * (‖intRowFamily t.b k‖+1) := h
        _ ≤ (2:ℝ)^(2*H+2) * (2:ℝ)^((2*H+2)*a+H) :=
          mul_le_mul (column_growth_factor H) hnorm (by positivity) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; ring
  obtain ⟨a,ha,_,_,_,hother,hnorm⟩ := passState_invariant ht P hbase hstep
  have hi : ‖intRowFamily t.b i‖ + 1 ≤ (2:ℝ)^((2*H+2)*n+H) := by
    by_cases he : i = k
    · subst i
      refine hnorm.trans (pow_le_pow_right₀ (by norm_num) ?_)
      have hl : a ≤ n := by have := k.isLt; omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hl) _
    · rw [hother i he]
      exact (hrow i).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hc := (PiLp.norm_apply_le (intRowFamily t.b i) l)
  rw [nativeRow_coordinate, Real.norm_eq_abs] at hc
  have hc' : |((t.b[i][l] : ℤ) : ℝ)| < (2:ℝ)^((2*H+2)*n+H) := by linarith
  have hz : |t.b[i][l]| < (2:ℤ)^((2*H+2)*n+H) := by exact_mod_cast hc'
  rw [Int.abs_eq_natAbs] at hz
  exact Nat.size_le.mpr (by exact_mod_cast hz)

end Lattice
end LinearProgramming
end Optimization
end OAI
