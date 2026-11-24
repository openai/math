import OAI.Computability.VPVNP.LiveEvaluatorRAMImage
import OAI.Computability.VPVNP.LiveEvaluatorRAMSchedule

/-!
# Memory images after publishing an evaluator instruction

The native preparation writes the five instruction registers in scratch. A
disjoint configuration still decodes to the same bounded evaluator state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM (Word Memory)
open PrimedStackRAM (Regs)
open UniversalMachine (Symbol Instruction)
open LiveEvaluatorRAMPrepare (scratchMemory scratchMemory_at scratchMemory_outside carryRegs selectedRegs)
open scoped Fin.CommRing

variable {w M extra : ℕ}

/-- The five register values published by preparation constitute the memory
image read by all subsequent scheduled cells. -/
theorem actionAt_scratch {rs : Regs w 32} {m : Memory w} {target : ℕ}
    {firstWrite firstMove secondWrite secondMove : Symbol}
    (h1 : (rs 1).val = 1) (hs : (rs 25).val + 5 ≤ 2 ^ w)
    (h5 : (rs 5).val = target) (h6 : (rs 6).val = firstWrite.val)
    (h7 : (rs 7).val = firstMove.val) (h8 : (rs 8).val = secondWrite.val)
    (h9 : (rs 9).val = secondMove.val) :
    ActionAt (scratchMemory rs m) (rs 25) target firstWrite firstMove secondWrite secondMove := by
  have h (i : Fin 5) :
      (scratchMemory rs m (rs 25 + (i.val : Word w)).val).val = (rs ⟨5 + i.val, by omega⟩).val := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    exact congrArg Fin.val (scratchMemory_at rs m h1 hs i)
  exact ⟨by simpa using (h 0).trans h5, (h 1).trans h6, (h 2).trans h7,
    (h 3).trans h8, (h 4).trans h9⟩

/-- Carrying an accepting evaluator publishes state one and four zero tape fields. -/
theorem actionAt_carryRegs (rs : Regs w 32) (m : Memory w) (h0 : (rs 0).val = 0)
    (h1 : (rs 1).val = 1) (hs : (rs 25).val + 5 ≤ 2 ^ w) :
    ActionAt (scratchMemory (carryRegs rs) m) (rs 25) 1 0 0 0 0 :=
  actionAt_scratch (rs := carryRegs rs) h1 hs h1 h0 h0 h0 h0

/-- A selected table slot publishes all five fields of that instruction. -/
theorem actionAt_selectedRegs (rs : Regs w 32) (m : Memory w) (a : Instruction extra)
    (hw : 2 ≤ w) (hcap : extra + 2 ≤ 2 ^ w) (h1 : (rs 1).val = 1)
    (hs : (rs 25).val + 5 ≤ 2 ^ w) :
    ActionAt (scratchMemory (selectedRegs rs m a) m) (rs 25) a.target.val
      a.firstSymbol a.firstMove a.secondSymbol a.secondMove := by
  obtain ⟨h5, h6, h7, h8, h9⟩ := LiveEvaluatorRAMDispatch.instructionRegs_fields
    (Function.update (LiveEvaluatorRAMPrepare.rowRegs rs m) 4 0) a hw hcap
  exact actionAt_scratch (rs := selectedRegs rs m a) h1 hs h5 h6 h7 h8 h9

/-- Configuration and scratch can be allocated in either order. The fit
bounds ensure that neither block wraps in machine-word arithmetic. -/
theorem ConfigAt.after_scratch {m : Memory w} {base : Word w} {c : LiveEvaluatorEncoding.Code extra M}
    (hc : ConfigAt m base c) (rs : Regs w 32) (h1 : (rs 1).val = 1)
    (hs : (rs 25).val + 5 ≤ 2 ^ w) (hfit : base.val + Schedule.calls M ≤ 2 ^ w)
    (hdis : base.val + Schedule.calls M ≤ (rs 25).val ∨ (rs 25).val + 5 ≤ base.val) :
    ConfigAt (scratchMemory rs m) base c := by
  have h (i : ℕ) (hi : i < Schedule.calls M) :
      scratchMemory rs m (base + (i : Word w)).val = m (base + (i : Word w)).val := by
    apply scratchMemory_outside rs m h1 hs
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  constructor
  · have hz : scratchMemory rs m base.val = m base.val := by
      simpa using h 0 (by simp [Schedule.calls])
    rw [hz, hc.state]
  · intro i
    have hf := h (1 + i.val) (by unfold Schedule.calls; omega)
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at hf
    rw [hf, hc.first]
  · intro i
    have hf := h (1 + (2 * M + 1) + i.val) (by unfold Schedule.calls; omega)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ← add_assoc, ← add_assoc] at hf
    rw [hf, hc.second]

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
