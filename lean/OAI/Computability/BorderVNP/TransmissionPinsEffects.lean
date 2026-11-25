import OAI.Computability.BorderVNP.TransmissionPins
import OAI.Computability.BorderVNP.DiagonalResidueRAMSteps
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Store and choice effects of the pin preparation loop -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (effect effect_runs)
open private deterministic_atom_bits from OAI.Computability.BorderVNP.RoutingISADeterministic

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Deterministic native fragments have empty choice strings. -/
theorem noChoices {c s m es t mt} (r : Runs pub macros c s m es t mt)
    (h : c.deterministic = true) : es.flatMap TeamRAM.Event.choices = [] := by
  induction r with
  | atom _ _ hs => simp [deterministic_atom_bits h hs]
  | seq _ _ a b =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp [a ha, b hb]
  | ifEq _ ih | ifLt _ ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp [tick, ih (by split <;> assumption)]
  | choose => contradiction
  | whileDone => rfl
  | whileStep _ _ _ a b => simp [tick, a h, b h]

/-- All twelve persistent register words are unchanged. -/
def SamePrefix (s t : Bank w) : Prop := ∀ i : Reg, i.val < 12 → t i = s i

/-- Straight-line suffix of the real-index branch, once the live word has been fetched. -/
def realTail : Code := .block [.binary .add 16 10 6, .store 16 14,
  .choose (.copy 15 1) (.copy 15 2)]

/-- Write the substituted value, then increment the loop cursor. -/
def stepTail : Code := .block [.binary .add 16 9 6, .store 16 15, .binary .add 6 6 1]

/-- The real branch writes the physical input word to the live-column array and makes
exactly one private guess, recording it in register 15. -/
theorem realTail_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (b : Bool) :
    ∃ es t, Runs pub macros realTail s m es t (Function.update m (s 10+s 6).val (s 14)) ∧
      traceCost es = 4 ∧ es.flatMap TeamRAM.Event.choices = [b] ∧ SamePrefix s t ∧
      t 15 = (if b then s 1 else s 2) := by
  let z := effect b s m realTail
  have rr := effect_runs pub macros b s m realTail (by decide)
  refine ⟨z.trace, z.bank, ?_, ?_, ?_, ?_, ?_⟩
  · cases b <;> simpa [z, realTail, Code.block, effect, BinaryOp.eval, Function.update] using rr
  · cases b <;> rfl
  · cases b <;> rfl
  · intro i hi
    have h16 : i ≠ 16 := by intro e; subst i; omega
    have h15 : i ≠ 15 := by intro e; subst i; omega
    cases b <;> simp [z, realTail, Code.block, effect, h16, h15]
  · cases b <;> simp [z, realTail, Code.block, effect, Function.update]

/-- The common suffix changes exactly the designated scratch entry and the cursor in the
persistent register prefix. The increment is the native word addition. -/
theorem stepTail_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) :
    ∃ es t, Runs pub macros stepTail s m es t (Function.update m (s 9+s 6).val (s 15)) ∧
      traceCost es = 3 ∧ es.flatMap TeamRAM.Event.choices = [] ∧
      SamePrefix (Function.update s 6 (s 6+s 1)) t := by
  let z := effect false s m stepTail
  have rr := effect_runs pub macros false s m stepTail (by decide)
  refine ⟨z.trace, z.bank, ?_, rfl, rfl, ?_⟩
  · simpa [z, stepTail, Code.block, effect, BinaryOp.eval, Function.update] using rr
  · intro i hi
    have h16 : i ≠ 16 := by intro e; subst i; omega
    by_cases he : i = 6 <;> simp [z, stepTail, Code.block, effect, BinaryOp.eval, he, h16]

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
