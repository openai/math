import OAI.ThreeFlat.RAM.TickGenerateTable
import OAI.ThreeFlat.RAM.HistoryFactorLibrary
import OAI.ThreeFlat.RAM.LiteralTable

namespace OAI
/-! # Installing the shared coefficient library from the fixed tick text -/

namespace ThreeFlat.RAM.TickLUTSeed
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan HistoryFactors BitLayout
open scoped Fin.CommRing

variable {F : Type*} {w k t p r : ℕ}

def entry (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F) (a : ℕ) : Word w :=
  if hi : a < 8*t then code.encode (table ⟨a/8,by omega⟩ (bits (a%8))) else 0

def expr (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F) (base : ℕ) : Term w k 1 :=
  LiteralTable.atIndex (entry code table) (8*t) (.binary .sub (.result 0) (.literal (base : Word w)))

theorem expr_binds (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F) (base : ℕ) :
    (expr (k:=k) code table base).binds = 3*(8*t)+3 := by
  simp [expr,Term.binary,Term.literal,Term.binds]


theorem generate (M : Machine w p r k) (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F)
    (base : ℕ) (fit : base+8*t < 2^w) (m : Memory w) (c : Config w p r)
    (P : Fin ((expr (k:=k) code table base).labels+6) → Fin p)
    (R : Fin (4+(expr (k:=k) code table base).binds) ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (P i) = TickGenerateTable.emit (expr code table base) (base : Word w)
      (base+8*t : ℕ) P R exit i)
    (start : c.pc = TickGenerateTable.driver (expr (k:=k) code table base) P 0) :
    let seeded := fillSegment base (8*t) (fun a => entry code table (a-base)) m
    ∃ steps ≤ 4+(8*t)*(6*(8*t)+10), ∃ out : Config w p r, out.pc = exit ∧
      advance M.program steps c m = some (out,seeded) ∧
      ∀ (i : Fin t) (j : Fin 8), seeded (base+8*i.val+j.val) = code.encode (table i (bits j.val)) := by
  intro seeded
  let e := expr (k:=k) code table base
  have b : (base : Word w).val = base := Fin.val_cast_of_lt (by omega)
  have z : ((base+8*t : ℕ) : Word w).val = base+8*t := Fin.val_cast_of_lt fit
  obtain ⟨steps,cost,out,pc,advance⟩ := TickGenerateTable.generate e M (base : Word w)
    (base+8*t : ℕ) P R exit rom (8*t) (by rw [b,z]) (fun a => entry code table (a-base))
    c m start (by
      intro x mm lo hi _
      rw [b] at lo
      rw [z] at hi
      apply LiteralTable.atIndex_eval _ _ _ (by omega) (by omega)
      change x-(base : Word w) = ((x.val-base : ℕ) : Word w)
      rw [Nat.cast_sub lo]
      simp)
  rw [b] at advance
  have ce : e.steps = 6*(8*t)+7 := by
    rw [Term.steps_eq,expr_binds]
    omega
  rw [ce] at cost
  refine ⟨steps,by simpa [Nat.add_assoc] using cost,out,pc,advance,?_⟩
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  have loc : base+8*i.val+j.val-base = 8*i.val+j.val := by omega
  simp [seeded,fillSegment,entry,loc,show base ≤ base+8*i.val+j.val by omega,show base+8*i.val+j.val < base+8*t by omega,
    show 8*i.val+j.val < 8*t by omega,show (8*i.val+j.val)/8=i.val by omega,
    show (8*i.val+j.val)%8=j.val by omega]

end ThreeFlat.RAM.TickLUTSeed

end OAI
