import OAI.Computability.VPVNP.CompressorRecordTable
import OAI.Computability.VPVNP.MotifAdmission
import OAI.Computability.VPVNP.ShrinkEnergy

/-!
# Computing the common layout from two word counters

In the second descriptor scan of Appendix E, each term contributes its squared supply
widths to two totals. Clearing the fixed denominators yields nonnegative integers, and
the common positive arc mass cancels. One native word block accumulates an edge's
contribution with two probes. One comparison of the two counters picks the same layout
as the real energy comparison of §7.2, including the tie case.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression.ShrinkEnergy

variable {M T : Type*} [Fintype M] [Fintype T]

/-- Integral score accumulated for the selected payloads in one layout. -/
def layoutScore (q : T → ℚ) (width : M → Bool → T → ℕ) (l : Bool) : ℕ :=
  ∑ m, MotifAdmission.energy q (width m l)

/-- The finite program chooses `true` only on strict improvement. -/
def selectLayout (q : T → ℚ) (width : M → Bool → T → ℕ) : Bool :=
  decide (layoutScore q width true < layoutScore q width false)

theorem layoutScore_energy (q : T → ℚ) (hq : ∀ e, 0 < q e) (width : M → Bool → T → ℕ)
    (p : ℝ) (l : Bool) :
    groupEnergy p (fun i => (q i : ℝ)) width l =
      (layoutScore q width l : ℝ) / ((MotifAdmission.denominator q : ℝ) * p) := by
  rw [groupEnergy, layoutScore, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := MotifAdmission.norm_sq_eq q hq (width m l)
  rw [MotifGrid.norm_sq (MotifGrid.realWidths q) _ (fun e => Rat.cast_pos.mpr (hq e))] at h
  rw [← div_div, ← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [div_div, mul_comm]
  rfl

theorem selectLayout_eq (q : T → ℚ) (hq : ∀ e, 0 < q e) (width : M → Bool → T → ℕ)
    (p : ℝ) (hp : 0 < p) : selectLayout q width = chosenLayout p (fun i => (q i : ℝ)) width := by
  have hcmp : groupEnergy p (fun i => (q i : ℝ)) width false ≤
      groupEnergy p (fun i => (q i : ℝ)) width true ↔
      layoutScore q width false ≤ layoutScore q width true := by
    rw [layoutScore_energy q hq width p, layoutScore_energy q hq width p,
      div_le_div_iff_of_pos_right (mul_pos (Nat.cast_pos.mpr (MotifAdmission.denominator_pos _)) hp),
      Nat.cast_le]
  by_cases h : layoutScore q width false ≤ layoutScore q width true
  · simp [selectLayout, chosenLayout, hcmp.mpr h, not_lt_of_ge h]
  · simp [selectLayout, chosenLayout, (mt hcmp.mp h), lt_of_not_ge h]

theorem layoutScore_le (q : T → ℚ) (width : M → Bool → T → ℕ) (W : ℕ)
    (hW : ∀ m l e, width m l e ≤ W) (l : Bool) :
    layoutScore q width l ≤ Fintype.card M * (∑ e, MotifAdmission.weight q e) * W ^ 2 := by
  unfold layoutScore MotifAdmission.energy
  calc
    _ ≤ ∑ _m : M, ∑ e, MotifAdmission.weight q e * W ^ 2 := by gcongr; apply hW
    _ = _ := by simp [← Finset.sum_mul, mul_assoc]

/-- Register 0 holds the score address, 1 the integer weight and 2 the payload width.
Registers 3 and 4 are temporaries. The same code updates either layout score. -/
def accumulateScore : List (Op 5 0) :=
  [.read 3 0, .binary .mul 4 2 2, .binary .mul 4 1 4,
    .binary .add 3 3 4, .write 0 3]

theorem accumulateScore_trace {w : ℕ} (pub : Fin 0 → Word w) (state : Word w)
    (regs : Regs w 5) (mem : Memory w) :
    let total := mem (regs 0).val + regs 1 * (regs 2 * regs 2)
    ∃ es rs, trace pub state accumulateScore regs mem =
        some (es, rs, writeMemory mem (regs 0) total) ∧
      countProbes es = 2 ∧ es.length = 5 ∧ rs 3 = total := by
  simp (config := {decide := true}) [accumulateScore, trace, Op.effect, BinaryOp.eval,
    Function.update, countProbes]

/-- A word counter gives the exact natural score while the final sum fits in one word. -/
theorem scoreWord_exact {w : ℕ} (old weight width : Word w)
    (hfit : old.val + weight.val * width.val ^ 2 < 2 ^ w) :
    (old + weight * (width * width)).val = old.val + weight.val * width.val ^ 2 := by
  simp only [Fin.val_add, Fin.val_mul, Nat.mul_mod_mod, Nat.add_mod_mod, pow_two]
  exact Nat.mod_eq_of_lt (by simpa [pow_two] using hfit)

/-- The exact finite opcode table realizes the score update from supplied registers. -/
theorem accumulateScore_native {w : ℕ} (pub : Fin 0 → Word w) (state : Word w)
    (regs : Regs w 5) (priv : Word w → Word w) (mem : Memory w) :
    let machine := (template accumulateScore 3).instantiate w pub
    let total := mem (regs 0).val + regs 1 * (regs 2 * regs 2)
    ∃ es, execute machine.program 6 ⟨machine.entry, state, regs, priv⟩ mem [] =
      some ⟨es, some total⟩ ∧ countProbes es = 2 ∧ es.length = 5 := by
  obtain ⟨es, rs, ht, hprobes, hlen, hreg⟩ := accumulateScore_trace pub state regs mem
  refine ⟨es, ?_, hprobes, hlen⟩
  change execute _ (1 + accumulateScore.length) _ mem [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hreg]

end CompressorRecords

end VPVNP
end Computability
end OAI
