import OAI.Computability.VPVNP.PrimedCounterAdminExec
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

/-!
# Writing an advice frame with reserved holes

Register 22 points at the first frame word and register 1 holds the stride.
A present slot writes its source register, while a hole leaves memory intact.
Both advance the cursor by the same stride.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceFrames

open BurstRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- A static schedule of register stores and holes. -/
def storeFlow : List (Option (Fin 32)) → Flow 32 11
  | [] => .line (.guardEq 0 0)
  | none :: rest => .seq (.line (.binary .add 22 22 1)) (storeFlow rest)
  | some r :: rest => .seq (.line (.write 22 r)) (.seq (.line (.binary .add 22 22 1)) (storeFlow rest))

private def advance (rs : Regs w 32) := Function.update rs 22 (rs 22 + rs 1)

/-- Advance the frame-writing cursor once per slot, including reserved holes, to obtain the
registers after publication. -/
def storeRegs : List (Option (Fin 32)) → Regs w 32 → Regs w 32
  | [], rs => rs
  | _ :: rest, rs => storeRegs rest (advance rs)

/-- The memory after writing each present register word into its frame slot and advancing over
reserved holes. -/
def frameMemory : List (Option (Fin 32)) → Regs w 32 → Memory w → Memory w
  | [], _, m => m
  | none :: rest, rs, m => frameMemory rest (advance rs) m
  | some r :: rest, rs, m => frameMemory rest (advance rs) (writeMemory m (rs 22) (rs r))

/-- The chronological frame writes and cursor-advance ticks for the given slot assignment. -/
def storeEvents : List (Option (Fin 32)) → Regs w 32 → List (Event w)
  | [], _ => [.tick]
  | none :: rest, rs => .tick :: storeEvents rest (advance rs)
  | some r :: rest, rs => .write (rs 22) (rs r) :: .tick :: storeEvents rest (advance rs)

/-- Exact registers, external memory and events after the fixed instruction schedule. -/
theorem store_exec (pub : Fin 11 → Word w) (st : Word w) (slots : List (Option (Fin 32)))
    (rs : Regs w 32) (m : Memory w) :
    Flow.Exec pub st (storeFlow slots) rs m (storeEvents slots rs) (storeRegs slots rs) (frameMemory slots rs m) := by
  induction slots generalizing rs m with
  | nil => exact .line (by simp [Op.effect, storeRegs, frameMemory])
  | cons slot rest ih =>
    cases slot with
    | none => exact (Flow.Exec.line rfl).seq (ih (advance rs) m)
    | some r => exact (Flow.Exec.line rfl).seq ((Flow.Exec.line rfl).seq (ih (advance rs) _))

theorem storeRegs_other (slots : List (Option (Fin 32))) (rs : Regs w 32) (r : Fin 32) (hr : r ≠ 22) :
    storeRegs slots rs r = rs r := by
  induction slots generalizing rs with
  | nil => rfl
  | cons x xs ih => exact (ih _).trans (Function.update_of_ne hr ..)

theorem storeRegs_cursor (slots : List (Option (Fin 32))) (rs : Regs w 32) :
    storeRegs slots rs 22 = rs 22 + (slots.length : Word w) * rs 1 := by
  induction slots generalizing rs with
  | nil => simp [storeRegs]
  | cons x xs ih =>
    rw [storeRegs, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    change rs 22 + rs 1 + (xs.length : Word w) * rs 1 = _
    ring

theorem storeEvents_counts (slots : List (Option (Fin 32))) (rs : Regs w 32) :
    choiceBits (storeEvents slots rs) = [] ∧ countProbes (storeEvents slots rs) = (slots.filterMap id).length ∧
      (storeEvents slots rs).length = slots.length + (slots.filterMap id).length + 1 := by
  induction slots generalizing rs with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons slot rest ih =>
    obtain ⟨hb, hp, hl⟩ := ih (advance rs)
    cases slot <;> simp [storeEvents, countProbes, choiceBits, hb, hp, hl] <;> omega

/-- The natural-address version of the same sequence, using the fixed entry
bank for all source registers. -/
private def naturalMemory : List (Option (Fin 32)) → Regs w 32 → ℕ → Memory w → Memory w
  | [], _, _, m => m
  | none :: rest, rs, base, m => naturalMemory rest rs (base+1) m
  | some r :: rest, rs, base, m => naturalMemory rest rs (base+1) (Function.update m base (rs r))

private theorem natural_eq (slots : List (Option (Fin 32))) (rs source : Regs w 32) (m : Memory w)
    (hsrc : ∀ r, some r ∈ slots → rs r = source r) (hno : some 22 ∉ slots)
    (h1 : (rs 1).val = 1) (hfit : (rs 22).val + slots.length ≤ 2 ^ w) :
    frameMemory slots rs m = naturalMemory slots source (rs 22).val m := by
  induction slots generalizing rs m with
  | nil => rfl
  | cons slot rest ih =>
    have hn : some (22 : Fin 32) ∉ rest := fun h => hno (List.mem_cons_of_mem _ h)
    have hsrc' (r : Fin 32) (hr : some r ∈ rest) : advance rs r = source r := by
      have hne : r ≠ 22 := fun h => hn (h ▸ hr)
      exact (Function.update_of_ne hne ..).trans (hsrc _ (List.mem_cons_of_mem _ hr))
    have hw (r : Fin 32) : writeMemory m (rs 22) (rs r) = Function.update m (rs 22).val (rs r) := by
      funext a
      by_cases h : a = (rs 22).val <;> simp [writeMemory, h]
    by_cases hnil : rest = []
    · subst rest
      cases slot with
      | none => rfl
      | some r => rw [frameMemory, naturalMemory, hw, hsrc r (by simp)]; rfl
    · have hpos : 0 < rest.length := List.length_pos_iff.mpr hnil
      have hv : (advance rs 22).val = (rs 22).val + 1 := by
        change (rs 22 + rs 1).val = _
        simp only [List.length_cons] at hfit
        rw [Fin.val_add, h1, Nat.mod_eq_of_lt (by omega)]
      have hf : (advance rs 22).val + rest.length ≤ 2^w := by rw [hv]; simp only [List.length_cons] at hfit; omega
      cases slot with
      | none => rw [frameMemory, naturalMemory, ih _ _ hsrc' hn h1 hf, hv]
      | some r => rw [frameMemory, naturalMemory, ih _ _ hsrc' hn h1 hf, hv, hw, hsrc r (by simp)]

private theorem natural_outside (slots : List (Option (Fin 32))) (rs : Regs w 32) (m : Memory w)
    (base a : ℕ) (ha : a < base ∨ base + slots.length ≤ a) :
    naturalMemory slots rs base m a = m a := by
  induction slots generalizing base m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at ha
    cases x with
    | none => exact ih _ _ (by omega)
    | some r => exact (ih _ _ (by omega)).trans (Function.update_of_ne (by omega : a ≠ base) ..)

/-- Words outside the frame survive every write. -/
theorem frameMemory_outside (slots : List (Option (Fin 32))) (rs : Regs w 32) (m : Memory w)
    (h1 : (rs 1).val = 1) (hfit : (rs 22).val + slots.length ≤ 2^w) (hno : some 22 ∉ slots)
    (a : ℕ) (ha : a < (rs 22).val ∨ (rs 22).val + slots.length ≤ a) : frameMemory slots rs m a = m a := by
  rw [natural_eq slots rs rs m (fun _ _ => rfl) hno h1 hfit]
  exact natural_outside slots rs m _ a ha

private theorem natural_at (slots : List (Option (Fin 32))) (rs : Regs w 32) (m : Memory w)
    (base i : ℕ) (hi : i < slots.length) :
    naturalMemory slots rs base m (base+i) = (slots[i].map rs).getD (m (base+i)) := by
  induction slots generalizing base i m with
  | nil => simp at hi
  | cons slot rest ih =>
    cases i with
    | zero =>
      cases slot <;> rw [naturalMemory, natural_outside rest rs _ _ _ (by omega)]
      · rfl
      · simp
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      have he : base + (i+1) = base+1+i := by omega
      cases slot with
      | none => rw [naturalMemory, he, ih _ _ _ hi']; rfl
      | some r =>
        rw [naturalMemory, he, ih _ _ _ hi', Function.update_of_ne (by omega : base+1+i ≠ base)]
        rfl

/-- A written slot reads back its entry register, while a hole reads back the entry memory. -/
theorem frameMemory_at (slots : List (Option (Fin 32))) (rs : Regs w 32) (m : Memory w)
    (h1 : (rs 1).val = 1) (hfit : (rs 22).val + slots.length ≤ 2^w) (hno : some 22 ∉ slots)
    (i : ℕ) (hi : i < slots.length) :
    frameMemory slots rs m ((rs 22).val+i) = (slots[i].map rs).getD (m ((rs 22).val+i)) := by
  rw [natural_eq slots rs rs m (fun _ _ => rfl) hno h1 hfit]
  exact natural_at slots rs m _ i hi

end LiveEvaluatorAdviceFrames

end VPVNP
end Computability
end OAI
