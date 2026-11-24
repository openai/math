import OAI.Computability.VPVNP.RAMTapeSortOneStageModel
import OAI.Computability.VPVNP.RAMParameters

/-! # Pathwise clock for the physical sorting passes -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortStages

open BurstRAM Filter

/-- Includes every phase update, row scan, split and array reversal. -/
def ticks (h d w : ℕ) :=
  (h+d)*((SortOneStage.budget h d w+6)*(h+d)+5)+1

/-- The sorting part of the physical stack computation fits a fixed power
when the address and word lengths fit in `n` and the block has at most
eight records per input bit. -/
theorem ticks_le {n h d w : ℕ} (hn : 4000010 ≤ n) (hb : 2^h ≤ 8*n)
    (ha : h+d ≤ n) (hw : w ≤ n) : ticks h d w ≤ n^6 := by
  have h₁ : (2^h+1)^2 ≤ (9*n)^2 := Nat.pow_le_pow_left (by omega) _
  have h₂ : h+d+w+1 ≤ 3*n := by omega
  have hl := (SortOneStage.budget_le h d w).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 16384 h₁) h₂)
  have hp : SortOneStage.budget h d w + 6 ≤ 4000000*n^3 := by
    rw [show 16384*(9*n)^2*(3*n)=3981312*n^3 by ring] at hl
    have hpos : 0 < n^3 := pow_pos (by omega) _
    omega
  calc
    ticks h d w ≤ n*((4000000*n^3)*n+5)+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul ha (Nat.add_le_add_right (Nat.mul_le_mul hp ha) _)) _
    _ = 4000000*n^5 + 5*n + 1 := by ring
    _ ≤ 4000010*n^5 := by
      have hsmall : n ≤ n^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<n) (by decide : 1 ≤ 5)
      omega
    _ ≤ n^6 := by rw [show n^6=n*n^5 by ring]; exact Nat.mul_le_mul_right _ hn

/-- In the paper's live construction the constant `B` only affects the
length threshold. The bound applies to every raw incident assignment. -/
theorem eventually_ticks_le (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ e, 2^e ≤ 2*n →
      ticks (2+e) (addressWidth B n) ((addressWidth B n + 10)^4) ≤ n^6 := by
  filter_upwards [eventually_word_stage_le B (B+4), eventually_ge_atTop 4000010] with n hstage hn e he
  have hd : addressWidth B n ≤ B*(n.log2+1) := Nat.mul_le_mul_left _ (clog_le_log2_succ n)
  have hpower : 2^e ≤ 2^(Nat.clog 2 n + 1) :=
    he.trans (by rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_right 2 (Nat.le_pow_clog (by decide : 1 < 2) n))
  have hbits := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower
  have hst : 2+e+addressWidth B n ≤ (B+4)*(n.log2+1) := by
    rw [Nat.add_mul]
    have := clog_le_log2_succ n
    omega
  obtain ⟨hw, ha⟩ := hstage _ _ hd hst
  exact ticks_le hn (by rw [pow_add]; omega) ha hw

end RAMTape.SortStages

end VPVNP
end Computability
end OAI
