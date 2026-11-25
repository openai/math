import OAI.ThreeFlat.RAM.ContractionMemory
import OAI.ThreeFlat.RAM.LiteralTable

namespace OAI
/-! # Native scalar library for a finite row template -/

namespace ThreeFlat.RAM.StableCompactLibrary
open Computability.VPVNP.BurstRAM DescriptorExpr BitLayout
open scoped Fin.CommRing

variable {F : Type*} {c w k : ℕ}

/-- Eight little-endian coefficient entries per template row. -/
def value (T : Fin c → (Fin 3 → Bool) → F) (code : FieldCode F w) (a : ℕ) : Word w :=
  if ht : a/8 < c then code.encode (T ⟨a/8,ht⟩ (bits (a%8))) else 0

theorem value_at (T : Fin c → (Fin 3 → Bool) → F) (code : FieldCode F w) (t : Fin c)
    (j : Fin 8) : value T code (8*t.val+j.val) = code.encode (T t (bits j.val)) := by
  have div : (8*t.val+j.val)/8 = t.val := by
    simp [Nat.mul_add_div (by decide : 0<8),Nat.div_eq_of_lt j.isLt]
  have rem : (8*t.val+j.val)%8 = j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  simp [value,div,rem,t.isLt]

def program (T : Fin c → (Fin 3 → Bool) → F) (code : FieldCode F w) : Term w k 1 :=
  LiteralTable.lookup (value T code) (8*c)

theorem program_binds (T : Fin c → (Fin 3 → Bool) → F) (code : FieldCode F w) :
    (program (k:=k) T code).binds = 24*c+1 := by
  rw [program,LiteralTable.lookup_binds]; omega

theorem program_eval (T : Fin c → (Fin 3 → Bool) → F) (code : FieldCode F w) (t : Fin c)
    (j : Fin 8) (small : 8*c ≤ 2^w) (words : Fin k → Word w) (mem : Memory w)
    (vs : Fin 1 → Word w) (arg : vs 0 = ((8*t.val+j.val : ℕ) : Word w)) :
    (program T code).eval words mem vs = code.encode (T t (bits j.val)) := by
  have hi : 8*t.val+j.val < 8*c := by have := t.isLt; have := j.isLt; omega
  exact (LiteralTable.lookup_eval _ _ _ hi small words mem vs arg).trans (value_at T code t j)

end ThreeFlat.RAM.StableCompactLibrary

end OAI
