import OAI.Computability.VPVNP.RAMSerialization
import OAI.Computability.VPVNP.RAMRecordOrder
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Fixed-width keys for the transcript sorting network -/

namespace ThreeFlat.Diagonal.TraceSlots

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization

variable {w : ℕ}

def small (hw : 2 ≤ w) (n : Fin 4) : Word w :=
  ⟨n.val, n.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hw)⟩

/-- Fields are in most-significant-key order, with a distinguished padding
flag. The initialization bit is redundant and determined by the operation. -/
def fields (hw : 2 ≤ w) : Option (WordRecord w) → Fin 7 → Word w
  | none => ![small hw 1, 0, 0, 0, 0, 0, 0]
  | some r => ![0, r.address, (if r.kind = .init then 0 else small hw 1), r.startCost,
      r.ordinal, (match r.kind with | .init => 0 | .read => small hw 1 | .write => small hw 2),
      r.value]

def toOrdered (r : Option (WordRecord w)) : OrderedSlot (Word w) :=
  ⟨r.map WordRecord.record⟩

def keyLess {n : ℕ} (a b : Fin n → Word w) : List (Fin n) → Prop
  | [] => False
  | i :: l => a i < b i ∨ a i = b i ∧ keyLess a b l

def keyIndices : List (Fin 7) := [0,1,2,3,4,5,6]

private theorem word_lt_val (x y : Word w) : x < y ↔ x.val < y.val := Iff.rfl

theorem keyLess_iff (hw : 2 ≤ w) (a b : Option (WordRecord w)) :
    keyLess (fields hw a) (fields hw b) keyIndices ↔ toOrdered a < toOrdered b := by
  change _ ↔ (toOrdered a).code < (toOrdered b).code
  cases a with
  | none =>
    cases b with
    | none =>
      have hn (f : Fin 7 → Word w) (l : List (Fin 7)) : ¬ keyLess f f l := by
        induction l with
        | nil => simp [keyLess]
        | cons i l ih => simp [keyLess, ih]
      simp [hn]
    | some b =>
      have hout : ¬ (toOrdered (none : Option (WordRecord w))).code <
        (toOrdered (some b)).code := by simp [toOrdered, OrderedSlot.code]
      rw [iff_false_intro hout, iff_false]
      change ¬ (small hw 1 < (0 : Word w) ∨ small hw 1 = 0 ∧ _)
      rintro (hlt | ⟨he,_⟩)
      · exact Nat.not_lt_zero _ hlt
      · exact Nat.one_ne_zero (congrArg Fin.val he)
  | some a =>
    cases b with
    | none => simp [fields, keyLess, keyIndices, toOrdered, OrderedSlot.code, small,
        word_lt_val, -Fin.val_fin_lt]
    | some b =>
      cases a with | mk ka aa va ta oa =>
        cases b with | mk kb ab vb tb ob =>
          cases ka <;> cases kb <;>
            simp [fields, keyLess, keyIndices, toOrdered, OrderedSlot.code, Kind.code,
               Record.timestamp, WordRecord.record, small, Prod.Lex.toLex_lt_toLex,
               word_lt_val, -Fin.val_fin_lt, Fin.ext_iff] <;> tauto

theorem fields_injective (hw : 2 ≤ w) : Function.Injective (fields hw) := by
  intro a b h
  have hn (f : Fin 7 → Word w) (l : List (Fin 7)) : ¬ keyLess f f l := by
    induction l with
    | nil => simp [keyLess]
    | cons i l ih => simp [keyLess, ih]
  have hab := (keyLess_iff hw a b).mpr.mt (by rw [h]; exact hn _ _)
  have hba := (keyLess_iff hw b a).mpr.mt (by rw [h]; exact hn _ _)
  have he := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
  have hr := congrArg OrderedSlot.record he
  cases a <;> cases b <;> simp_all [toOrdered, WordRecord.record_injective.eq_iff]

end ThreeFlat.Diagonal.TraceSlots

end OAI
