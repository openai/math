import OAI.Computability.VPVNP.LiveEvaluatorRAMPrepareImage

/-!
# Preparing a transition from raw configuration words

A successful first call bounds the source state, verifies the proposed target
and publishes its instruction. Every word of both configuration blocks can
still be read at the same address after the call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM

open BurstRAM (Word Memory)
open PrimedStackRAM (Regs)
open UniversalMachine (Program Instruction)
open LiveEvaluatorRAMPrepare
open scoped Fin.CommRing

variable {w M : ℕ} {p : Program} {pub : Fin 4 → Word w} {m mem : Memory w} {bs : List Bool}

/-- Consequences of native preparation before either tape block has been decoded. -/
theorem Prepared.raw_facts (run : Prepared p pub m mem bs) (hl : PrepLayout p pub M) :
    0 < (m (pub 1).val).val ∧ (m (pub 1).val).val < p.extra + 2 ∧
    (∀ i < Schedule.calls M, mem (pub 1 + (i : Word w)).val = m (pub 1 + (i : Word w)).val) ∧
    (∀ i < Schedule.calls M, mem (pub 2 + (i : Word w)).val = m (pub 2 + (i : Word w)).val) ∧
    ∃ a : Instruction p.extra, 0 < a.target.val ∧ (m (pub 2).val).val = a.target.val ∧
      ActionAt mem (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove := by
  rw [Prepared, Schedule.initial_choices_iff] at run
  obtain ⟨es, reg, exec, _⟩ := run
  let rs : Regs w 32 := Schedule.loaded pub 0 (fun _ => 0) m
  obtain ⟨hp, hb, fs, s, sel, hpt, hout, _, _, rfl⟩ :=
    (prepare_exec_iff p pub 0 rs m hl.width hl.states rfl rfl es reg mem).mp exec
  change (m (pub 1).val).val ≤ p.extra + 1 at hb
  have h1 : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := hl.width; omega))
  have hs1 : (s 1).val = 1 := (congrArg Fin.val (sel.frame 1 (by decide))).trans h1
  have hs25 : s 25 = pub 3 := sel.frame 25 (by decide)
  have hsfit : (s 25).val + 5 ≤ 2 ^ w := hs25 ▸ hl.scratchFit
  have block (b : Word w) (hfit : b.val + Schedule.calls M ≤ 2 ^ w)
      (hdis : b.val + Schedule.calls M ≤ (pub 3).val ∨ (pub 3).val + 5 ≤ b.val)
      (i : ℕ) (hi : i < Schedule.calls M) :
      scratchMemory s m (b + (i : Word w)).val = m (b + (i : Word w)).val := by
    apply scratchMemory_outside s m hs1 hsfit
    rw [hs25, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨hp, by omega, block _ hl.oldFit hl.oldDisjoint, block _ hl.outFit hl.outDisjoint, ?_⟩
  have hs0 : s 0 = 0 := sel.frame 0 (by decide)
  have hs24 : s 24 = pub 2 := sel.frame 24 (by decide)
  rw [hs24] at hout
  rw [hs0] at hpt
  change 0 < (s 5).val at hpt
  let u := boundsRegs p rs
  cases sel with
  | carry =>
    exact ⟨LiveEvaluatorAction.carry _, Nat.zero_lt_one, (congrArg Fin.val hout).trans h1,
      actionAt_carryRegs u m rfl h1 hl.scratchFit⟩
  | slot _ _ _ bit a ha =>
    have ht : (selectedRegs u m a 5).val = a.target.val :=
      (LiveEvaluatorRAMDispatch.instructionRegs_fields _ a hl.width hl.states).1
    exact ⟨a, ht ▸ hpt, (congrArg Fin.val hout).trans ht,
      actionAt_selectedRegs u m a hl.width hl.states h1 hl.scratchFit⟩

end LiveEvaluatorRAM

end VPVNP
end Computability
end OAI
