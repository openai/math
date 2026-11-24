import OAI.Computability.VPVNP.PrimedCounterResources
import OAI.Computability.VPVNP.PrimedCounterData

/-!
# Instantiating the primed parser with the paper's word widths

Each nomination component has the paper's two-address-width encoding. The
private words in the parser also hold the absolute cursor and triangular index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Resources

open BurstRAM CursorBounds PrimedInputRAM PrimedStackRAM Compression

variable {B n states : ℕ} {δ : ℝ} {L : Lengths}
variable {Q : Layout L n (addressWidth B n) (liveBucket δ n) (CursorBounds.wordBits B n)}

/-- The scheduled body uses the absolute cursor counted in the numerical bounds. -/
theorem data_total (D : Data Q states) : D.total = callCount B n states := by
  have hn : 0 < n := (Nat.zero_le D.degree.val).trans_lt D.degree.isLt
  change Cursor.calls (_ + _) _ _ _ _ = _
  rw [← two_mul]
  exact callCount_eq B n states hn

/-- The actual private and external budgets of the instantiated pair call. -/
theorem Bounds.dataBudget (h : Bounds B n states Q.scratchBase) (D : Data Q states) :
    6 * D.fuel ≤ n^10 ∧ 15 * D.total ≤ 2 ^ virtualBits B n * 2 ^ roundedUp 1 4 n := by
  rw [data_total D]
  exact ⟨h.privateWork, h.total⟩

/-- A histogram component bounded by the entire traversal can still be
incremented without wrapping a parser word. -/
theorem Bounds.increment (h : Bounds B n states Q.scratchBase) {v : ℕ}
    (hv : v ≤ 2 * processorCount B n * (2*n-1)) :
    v + 1 < 2 ^ CursorBounds.wordBits B n := by
  have hbit : 2 * addressWidth B n < CursorBounds.wordBits B n := by
    change 2 * addressWidth B n < (addressWidth B n + 10)^4
    calc
      _ < (addressWidth B n + 10)^2 := by nlinarith [Nat.zero_le (addressWidth B n * addressWidth B n)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  exact (Nat.succ_le_of_lt (hv.trans_lt h.component)).trans_lt (Nat.pow_lt_pow_right (by decide) hbit)

/-- Assemble all hypotheses needed for concrete instruction correctness. -/
theorem Bounds.dataFits (h : Bounds B n states Q.scratchBase) (D : Data Q states)
    (hparams : Opcodes.ParameterFit Q) (hd : D.degree.val + 1 = n)
    (hh : Header.count L + D.labels ≤ Q.scratchBase)
    (hnom : ∀ a, D.nomination a < 2 ^ (2 * addressWidth B n)) : D.Fits := by
  have hword : 2 < 2 ^ CursorBounds.wordBits B n := by
    change 2^1 < 2^((addressWidth B n + 10)^4)
    apply Nat.pow_lt_pow_right (by decide)
    exact Nat.one_lt_pow (by decide) (by omega)
  exact ⟨hparams, hd, hh, h.scratch, h.states, hword, by simpa only [pow_two] using h.triangle,
    (data_total D) ▸ h.cursor, fun a => (hnom a).trans_le h.componentWord⟩

end PrimedCounter.Resources

end VPVNP
end Computability
end OAI
