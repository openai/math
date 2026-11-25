import OAI.Computability.NearSquareRoot.SynchronizedPhysicalBits
import OAI.Computability.NearSquareRoot.CoprimeBox
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Sparse width of a synchronized physical Walsh mask

At most one bit per block occurs in an emitted Walsh row. Each block uses at
least four axes except for the merged remainder in the partition, so the
number of designated bits already satisfies the recursive pass's sparsity
budget with constant one.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

/-- Every subset of the designated block bits satisfies the sparsity bound
for the uniform grouped traversal. -/
theorem selected_sparse {k : ℕ} (hb : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (hk : 2 ≤ k) (a : Finset (Fin ((CoprimeBox.box k).length/4))) :
    ((a.image (selectedPosition hb)).card : ℝ) ≤ 1*k / Real.log (2+k) := by
  have count : (a.image (selectedPosition hb)).card ≤ k / BoxScale.width k := by
    have hc := Finset.card_le_univ a
    rw [Fintype.card_fin] at hc
    have hb' := hb.axisCount
    have nonneg := Nat.zero_le (k / BoxScale.width k)
    have hq : (CoprimeBox.box k).length/4 ≤ k / BoxScale.width k := by omega
    exact Finset.card_image_le.trans (hc.trans hq)
  have prod : (a.image (selectedPosition hb)).card * BoxScale.width k ≤ k :=
    (Nat.mul_le_mul_right _ count).trans (Nat.div_mul_le_self ..)
  have w : Real.log (2+k) ≤ (BoxScale.width k : ℝ) := by
    have hc : 1 ≤ Nat.clog 2 k := Nat.clog_pos (by decide) (by omega)
    have p : (k:ℝ) ≤ (2:ℝ)^(Nat.clog 2 k) := by exact_mod_cast Nat.le_pow_clog (by decide : 1<2) k
    have hl : (2:ℝ)+k ≤ 2^(Nat.clog 2 k+1) := by
      rw [pow_succ]
      have h : (2:ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hlog := Real.log_le_log (by positivity : 0 < (2:ℝ)+k) hl
    rw [Real.log_pow] at hlog
    have hs : (Nat.clog 2 k:ℝ)+1 ≤ (BoxScale.width k:ℝ) := by exact_mod_cast (show Nat.clog 2 k+1 ≤ BoxScale.width k by unfold BoxScale.width; omega)
    calc
      _ ≤ ((Nat.clog 2 k+1:ℕ):ℝ)*Real.log 2 := hlog
      _ ≤ ((Nat.clog 2 k+1:ℕ):ℝ)*1 := mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]) (by positivity)
      _ ≤ _ := by simpa using hs
  apply (le_div_iff₀ (Real.log_pos (show 1 < (2:ℝ)+k by linarith [Nat.cast_nonneg (α:=ℝ) k]))).2
  exact (mul_le_mul_of_nonneg_left w (Nat.cast_nonneg _)).trans (by simpa using (show ((a.image (selectedPosition hb)).card : ℝ) * (BoxScale.width k : ℝ) ≤ k by exact_mod_cast prod))

end BoxFin

end NearSquareRoot
end Computability
end OAI
