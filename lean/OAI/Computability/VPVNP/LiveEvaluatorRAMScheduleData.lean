import OAI.Computability.VPVNP.LiveEvaluatorRAMSchedule
import OAI.Computability.VPVNP.LiveEvaluatorRAMCell
import OAI.Computability.VPVNP.LiveEvaluatorRAMImage

/-!
# Scheduled cell operands in the actual live configuration memory

The noninitial call numbers enumerate first the old cells of tape one and
then the old cells of tape two. Reconstructing the private registers from
each call number supplies exactly the operands required by the cell test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorRAM.Schedule

open BurstRAM PrimedStackRAM LiveEvaluatorEncoding
open scoped Fin.CommRing

variable {w M extra : ℕ}

/-- The one-based persistent call cursor for a selected tape and cell. -/
def cellCursor (second : Bool) (i : Fin (2 * M + 1)) :=
  (if second then 2 * M + 1 else 0) + i.val + 1

theorem cellCursor_lt_calls (second : Bool) (i : Fin (2 * M + 1)) :
    cellCursor second i < calls M := by
  cases second <;> simp [cellCursor, calls] <;> omega

theorem cellCursor_word_ne_zero (second : Bool) (i : Fin (2 * M + 1)) (hc : calls M < 2 ^ w) :
    (cellCursor second i : Word w) ≠ 0 := by
  have h := (cellCursor_lt_calls second i).trans hc
  rw [ne_eq, Fin.ext_iff, Fin.val_natCast, Nat.mod_eq_of_lt h, Fin.val_zero]
  simp [cellCursor]

/-- Every noninitial call below the accepting cursor visits exactly one
tape and cell. -/
theorem exists_unique_visit {c : ℕ} (hp : 0 < c) (hc : c < calls M) :
    ∃! x : Bool × Fin (2 * M + 1), cellCursor x.1 x.2 = c := by
  unfold calls at hc
  by_cases h : c ≤ 2 * M + 1
  · refine ⟨(false, ⟨c-1, by omega⟩), by simp [cellCursor]; omega, ?_⟩
    rintro ⟨b, j⟩ hj
    cases b <;> simp [cellCursor] at hj ⊢
    · apply Fin.ext; dsimp; omega
    · omega
  · refine ⟨(true, ⟨c - (2*M+1) - 1, by omega⟩), by simp [cellCursor]; omega, ?_⟩
    rintro ⟨b, j⟩ hj
    cases b <;> simp [cellCursor] at hj ⊢
    · omega
    · apply Fin.ext; dsimp; omega

/-- The literal selected tape, including the canonical blank tapes at halts. -/
def window (s : LiveEvaluatorEncoding.Code extra M) (second : Bool) : TapeWindow M :=
  ⟨if second then s.secondCell else s.firstCell⟩

/-- Reconstruct the register bank used by the elementary cell fragment. -/
def bank (pub : Pub → Word w) (rs : Regs w 32) (m : Memory w)
    (second : Bool) (i : Fin (2 * M + 1)) : Regs w 32 :=
  located (loaded pub (cellCursor second i : Word w) rs m) m

/-- The start address of the selected tape window within a serialized configuration. -/
def baseOf (addr : Word w) (M : ℕ) (second : Bool) : Word w :=
  if second then addr + 1 + ((2 * M + 1 : ℕ) : Word w) else addr + 1

/-- The instruction-scratch address of the proposed write symbol for the selected tape. -/
def writeAddr (addr : Word w) (second : Bool) := if second then addr + 3 else addr + 1

theorem bank_operands (pub : Pub → Word w) (rs : Regs w 32) (m : Memory w)
    (second : Bool) (i : Fin (2 * M + 1)) (hM : (pub 0).val = M) (hc : calls M < 2 ^ w) :
    let r := bank pub rs m second i
    r 0 = 0 ∧ r 1 = 1 ∧ r 3 = 3 ∧ r 5 = m (pub 3).val ∧
      r 6 = m (writeAddr (pub 3) second).val ∧ r 7 = m (writeAddr (pub 3) second + 1).val ∧
      r 11 = (M : Word w) ∧ r 12 = ((2 * M : ℕ) : Word w) ∧ r 13 = (i.val : Word w) ∧
      r 14 = baseOf (pub 1) M second ∧ r 15 = baseOf (pub 2) M second ∧ r 16 = m (pub 1).val := by
  have hM' : pub 0 = (M : Word w) := by rw [← hM, Fin.cast_val_eq_self]
  let N := 2 * M + 1
  have hN : N < 2 ^ w := by unfold N calls at *; omega
  have hNN : N + i.val < 2 ^ w := by have := i.isLt; unfold N calls at *; omega
  cases second with
  | false =>
    have hi : (cellCursor false i : Word w) - 1 = (i.val : Word w) := by simp [cellCursor]
    have hlt : (i.val : Word w) < (N : Word w) := by
      rw [Fin.lt_def, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans hN),
        Nat.mod_eq_of_lt hN]
      exact i.isLt
    have hh : (i.val : Word w) < (M : Word w) + M + 1 := by simpa [N, two_mul] using hlt
    simp (config := { decide := true }) [bank, located, loaded, install, baseOf, writeAddr,
      Function.update, hi, hh, hM', two_mul]
  | true =>
    have hi : (cellCursor true i : Word w) - 1 = ((N + i.val : ℕ) : Word w) := by simp [cellCursor, N]
    have hlt : ¬ ((N + i.val : ℕ) : Word w) < (N : Word w) := by
      rw [Fin.lt_def, Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt hNN, Nat.mod_eq_of_lt hN]
      omega
    have hh : ¬(M : Word w) + M + 1 + (i.val : Word w) < (M : Word w) + M + 1 := by
      simpa [N, two_mul] using hlt
    simp (config := { decide := true }) [bank, located, loaded, install, baseOf, writeAddr,
      Function.update, hi, hh, hM', N, two_mul]

/-- Every actual scheduled register bank refers to the right tape cells,
source and target states, and the instruction fields saved in scratch. -/
theorem scheduled_tape_data (pub : Pub → Word w) (rs : Regs w 32) (m : Memory w)
    (old out : LiveEvaluatorEncoding.Code extra M)
    (fw fm sw sm : UniversalMachine.Symbol) (second : Bool) (i : Fin (2 * M + 1))
    (hw : 2 ≤ w) (hM : (pub 0).val = M) (hc : calls M < 2 ^ w)
    (ho : ConfigAt m (pub 1) old) (hn : ConfigAt m (pub 2) out)
    (ha : ActionAt m (pub 3) out.stateWord.val fw fm sw sm) :
    let r := bank pub rs m second i
    TapeCellData r m (window old second) (window out second)
        (if second then sw else fw) (if second then sm else fm) i ∧
      (r 5).val = out.stateWord.val ∧ (r 16).val = old.stateWord.val := by
  let r := bank pub rs m second i
  obtain ⟨h0, h1, h3, h5, h6, h7, h11, h12, h13, h14, h15, h16⟩ := bank_operands pub rs m second i hM hc
  refine ⟨?_, (congrArg Fin.val h5).trans ha.targetVal, (congrArg Fin.val h16).trans ho.state⟩
  have h4 : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have hcap : 2 * M + 1 < 2 ^ w := by unfold calls at hc; omega
  constructor
  · rw [h0]; rfl
  · rw [h1]; exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 ^ w)
  · rw [h3]; exact Nat.mod_eq_of_lt (by omega : (3 : ℕ) < 2 ^ w)
  · rw [h6]; cases second <;> first | exact ha.firstWriteVal | exact ha.secondWriteVal
  · rw [h7]; cases second <;> simp only [writeAddr, Bool.false_eq_true, ↓reduceIte]
    · rw [show pub 3 + 1 + 1 = pub 3 + 2 by ring]; exact ha.firstMoveVal
    · rw [show pub 3 + 3 + 1 = pub 3 + 4 by ring]; exact ha.secondMoveVal
  · rw [h11, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · rw [h12, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  · rw [h13, Fin.val_natCast, Nat.mod_eq_of_lt (i.isLt.trans hcap)]
  · rw [h14, h13]; cases second <;> first | exact ho.first i | exact ho.second i
  · intro j f hj
    have he : j = (f.val : Word w) := by rw [← hj, Fin.cast_val_eq_self]
    rw [h15, he]; cases second <;> first | exact hn.first f | exact hn.second f

end LiveEvaluatorRAM.Schedule

end VPVNP
end Computability
end OAI
