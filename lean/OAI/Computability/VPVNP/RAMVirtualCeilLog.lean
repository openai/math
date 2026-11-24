import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import Mathlib.Data.Nat.Log

/-!
# Ceiling logarithm in the private word RAM

Each iteration replaces the operand by its rounded-up half. Registers zero and
one hold the constants one and two. Registers two and three hold the operand
and the iteration count. The terminal comparison is included in the cost.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.VirtualParameters

open PrivateRAM PrimedInputRAM PrimedStackRAM

variable {w k : ℕ}

/-- The three arithmetic instructions between successive loop tests. -/
private def clogStep : Flow 12 k :=
  .seq (.line (.binary .add 2 2 0))
    (.seq (.line (.binary .div 2 2 1)) (.line (.binary .add 3 3 0)))

/-- Repeated rounded-up halving of register two, counting in register three. -/
def clogLoop : Flow 12 k := .whileLt 0 2 clogStep

private theorem clogRunAux (pub : Fin k → Word w) (state : Word w) (m : Memory w)
    (x count : ℕ) (rs : Regs w 12) (hOne : (rs 0).val = 1) (hTwo : (rs 1).val = 2)
    (hOperand : (rs 2).val = x) (hCounter : (rs 3).val = count)
    (hx : x + 1 < 2 ^ w) (hc : count + Nat.clog 2 x < 2 ^ w) :
    ∃ out, Flow.Exec pub state clogLoop rs m (List.replicate (4 * Nat.clog 2 x + 1) .tick) out m ∧
      (out 2).val ≤ 1 ∧ (out 3).val = count + Nat.clog 2 x ∧
      ∀ i : Fin 12, i ≠ 2 → i ≠ 3 → out i = rs i := by
  induction x using Nat.strong_induction_on generalizing count rs with
  | h x ih =>
    by_cases h : x ≤ 1
    · rw [Nat.clog_of_right_le_one h, Nat.add_zero]
      exact ⟨rs, .whileDone (by change ¬ (rs 0).val < (rs 2).val; omega),
        hOperand.trans_le h, hCounter, fun _ _ _ => rfl⟩
    · let half := (x + 1) / 2
      have hhalf : half < x := by dsimp [half]; omega
      have hlog : Nat.clog 2 x = Nat.clog 2 half + 1 := by
        rw [Nat.clog_of_two_le Nat.one_lt_two (by omega : 2 ≤ x)]
        congr 2
      let a := Function.update rs (2 : Fin 12) (BinaryOp.add.eval (rs 2) (rs 0))
      let b := Function.update a (2 : Fin 12) (BinaryOp.div.eval (a 2) (a 1))
      let next := Function.update b (3 : Fin 12) (BinaryOp.add.eval (b 3) (b 0))
      have preserve (i : Fin 12) (h₂ : i ≠ 2) (h₃ : i ≠ 3) : next i = rs i := by
        simp [next, b, a, Function.update_of_ne h₂, Function.update_of_ne h₃]
      have ha : (a 2).val = x + 1 := by
        rw [show a 2 = rs 2 + rs 0 by simp [a, BinaryOp.eval],
          Fin.val_add_eq_of_add_lt (by omega), hOperand, hOne]
      have haOne : (a 1).val = 2 := by simpa [a, Function.update_apply] using hTwo
      have hquot : (BinaryOp.div.eval (a 2) (a 1)).val = (a 2).val / (a 1).val :=
        Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (a 2).isLt)
      have hnextOperand : (next 2).val = half := by
        rw [show next 2 = BinaryOp.div.eval (a 2) (a 1) by simp [next, b],
          hquot, ha, haOne]
      have hbCount : (b 3).val = count := by simpa [b, a, Function.update_apply] using hCounter
      have hbOne : (b 0).val = 1 := by simpa [b, a, Function.update_apply] using hOne
      have hnextCount : (next 3).val = count + 1 := by
        rw [show next 3 = b 3 + b 0 by simp [next, BinaryOp.eval],
          Fin.val_add_eq_of_add_lt (by omega), hbCount, hbOne]
      have step : Flow.Exec pub state clogStep rs m [.tick, .tick, .tick] next m :=
        Flow.Exec.seq (.line (rs' := a) rfl)
          (Flow.Exec.seq (.line (rs' := b) rfl) (.line (rs' := next) rfl))
      obtain ⟨out, run, small, value, keep⟩ := ih half hhalf (count + 1) next
        (by rw [preserve 0 (by decide) (by decide), hOne])
        (by rw [preserve 1 (by decide) (by decide), hTwo])
        hnextOperand hnextCount (by omega) (by omega)
      refine ⟨out, ?_, small, by omega, fun i h₂ h₃ => (keep i h₂ h₃).trans (preserve i h₂ h₃)⟩
      rw [show 4 * Nat.clog 2 x + 1 = (3 + (4 * Nat.clog 2 half + 1)) + 1 by omega,
        List.replicate_succ, List.replicate_add]
      exact Flow.Exec.whileStep (by change (rs 0).val < (rs 2).val; omega) step run

/-- Starting at zero the counter returns the ceiling logarithm. The only events
are ticks, and the loop retains every register except its operand and counter. -/
theorem clogRun (pub : Fin k → Word w) (state : Word w) (m : Memory w)
    (x : ℕ) (rs : Regs w 12) (hOne : (rs 0).val = 1) (hTwo : (rs 1).val = 2)
    (hOperand : (rs 2).val = x) (hCounter : (rs 3).val = 0)
    (hx : x + 1 < 2 ^ w) (hc : Nat.clog 2 x < 2 ^ w) :
    ∃ out, Flow.Exec pub state clogLoop rs m (List.replicate (4 * Nat.clog 2 x + 1) .tick) out m ∧
      (out 2).val ≤ 1 ∧ (out 3).val = Nat.clog 2 x ∧
      ∀ i : Fin 12, i ≠ 2 → i ≠ 3 → out i = rs i := by
  simpa using clogRunAux pub state m x 0 rs hOne hTwo hOperand hCounter hx (by simpa using hc)

end BurstRAM.VirtualParameters

end VPVNP
end Computability
end OAI
