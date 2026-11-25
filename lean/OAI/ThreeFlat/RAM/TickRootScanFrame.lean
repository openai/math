import OAI.ThreeFlat.RAM.TickSlotWrites
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Loading root ownership metadata and publishing the selected-root counters -/

namespace ThreeFlat.RAM.TickRootScanInit

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing

variable {w p r k : ℕ}

structure Layout where
  s1 : ℕ
  s6 : ℕ
  dst : ℕ
  ctl : ℕ

def loadRows (A : Layout) (P : Fin 9 → Fin p) (R : Fin 9 ↪ Fin r) (exit : Fin p)
    (i : Fin 9) : Instr w p r k :=
  match i.val with
  | 0 => .constant (R 1) ((A.s6+1 : ℕ) : Word w) (P 1)
  | 1 => .readExternal (R 1) (R 1) (P 2)
  | 2 => .constant (R 2) ((A.s6+4 : ℕ) : Word w) (P 3)
  | 3 => .readExternal (R 2) (R 2) (P 4)
  | 4 => .constant (R 3) (A.dst : Word w) (P 5)
  | 5 => .constant (R 5) (A.s1 : Word w) (P 6)
  | 6 => .readExternal (R 5) (R 5) (P 7)
  | 7 => .constant (R 6) ((A.s1+3 : ℕ) : Word w) (P 8)
  | _ => .readExternal (R 6) (R 6) exit

def loadBlock (w : ℕ) (A : Layout) : Block w 9 9 0 where
  first := 0
  emit P R _ exit := loadRows A P R exit

theorem advance_load (A : Layout) (M : Machine w p r k) (P : Fin 9 ↪ Fin p) (R : Fin 9 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (rom : (loadBlock w A).Installed M P R pub exit)
    (c : Config w p r) (m : Memory w) (start : c.pc = P 0)
    (s1Fit : A.s1+3 < 2^w) (s6Fit : A.s6+4 < 2^w) :
    ∃ d, advance M.program 9 c m = some (d,m) ∧ d.pc=exit ∧
      d.reg (R 1)=m (A.s6+1) ∧ d.reg (R 2)=m (A.s6+4) ∧ d.reg (R 3)=(A.dst : Word w) ∧
      d.reg (R 5)=m A.s1 ∧ d.reg (R 6)=m (A.s1+3) := by
  change ∀ i, M.code (P i) = loadRows A P R exit i at rom
  simp (config := {decide := true}) [advance,Machine.program,start,rom,loadRows,Instr.run,Config.put,
    Function.update,Fin.val_cast_of_lt s1Fit,Fin.val_cast_of_lt s6Fit,
    Fin.val_cast_of_lt (by omega : A.s1 < 2^w),Fin.val_cast_of_lt (by omega : A.s6+1 < 2^w),
    -Nat.cast_add]

def finishRows (A : Layout) (P : Fin 11 → Fin p) (R : Fin 9 ↪ Fin r) (exit : Fin p)
    (i : Fin 11) : Instr w p r k :=
  match i.val with
  | 0 => .constant (R 0) ((A.ctl+1 : ℕ) : Word w) (P 1)
  | 1 => .writeExternal (R 0) (R 4) (P 2)
  | 2 => .constant (R 1) 0 (P 3)
  | 3 => .constant (R 0) (A.ctl : Word w) (P 4)
  | 4 => .writeExternal (R 0) (R 1) (P 5)
  | 5 => .constant (R 0) ((A.ctl+2 : ℕ) : Word w) (P 6)
  | 6 => .writeExternal (R 0) (R 1) (P 7)
  | 7 => .constant (R 0) ((A.ctl+3 : ℕ) : Word w) (P 8)
  | 8 => .writeExternal (R 0) (R 1) (P 9)
  | 9 => .constant (R 0) ((A.ctl+4 : ℕ) : Word w) (P 10)
  | _ => .writeExternal (R 0) (R 4) exit

def finishBlock (w : ℕ) (A : Layout) : Block w 11 9 0 where
  first := 0
  emit P R _ exit := finishRows A P R exit

/-- Set the root ordinal, cumulative rows and hidden bits to zero. The stored
length and the initial countdown both equal the actual selected count. -/
def controls (A : Layout) (count : ℕ) (m : Memory w) : Memory w := fun j =>
  if j=A.ctl+4 then (count : Word w) else if j=A.ctl+3 then 0 else if j=A.ctl+2 then 0 else
  if j=A.ctl then 0 else if j=A.ctl+1 then (count : Word w) else m j

theorem advance_finish (A : Layout) (M : Machine w p r k) (P : Fin 11 ↪ Fin p) (R : Fin 9 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (rom : (finishBlock w A).Installed M P R pub exit)
    (c : Config w p r) (m : Memory w) (start : c.pc=P 0) (count : ℕ) (num : (c.reg (R 4)).val=count)
    (room : A.ctl+4 < 2^w) :
    ∃ d, advance M.program 11 c m = some (d,controls A count m) ∧ d.pc=exit := by
  change ∀ i, M.code (P i) = finishRows A P R exit i at rom
  have word : c.reg (R 4) = (count : Word w) := by rw [← num]; simp
  simp (config := {decide := true}) [advance,Machine.program,start,rom,finishRows,Instr.run,Config.put,
    Function.update,word,-Nat.cast_add]
  funext j
  simp only [writeMemory,controls,Fin.val_cast_of_lt room,Fin.val_cast_of_lt (by omega : A.ctl < 2^w),
    Fin.val_cast_of_lt (by omega : A.ctl+1 < 2^w),Fin.val_cast_of_lt (by omega : A.ctl+2 < 2^w),
    Fin.val_cast_of_lt (by omega : A.ctl+3 < 2^w)]


theorem controls_words (A : Layout) (count : ℕ) (m : Memory w) :
    let o := controls A count m
    o A.ctl=0 ∧ o (A.ctl+1)=(count : Word w) ∧ o (A.ctl+2)=0 ∧ o (A.ctl+3)=0 ∧
      o (A.ctl+4)=(count : Word w) := by
  simp [controls]

theorem controls_outside (A : Layout) (count : ℕ) (m : Memory w) (j : ℕ)
    (space : j < A.ctl ∨ A.ctl+5 ≤ j) : controls A count m j = m j := by
  simp [controls,show j≠A.ctl by omega,show j≠A.ctl+1 by omega,show j≠A.ctl+2 by omega,
    show j≠A.ctl+3 by omega,show j≠A.ctl+4 by omega]


end ThreeFlat.RAM.TickRootScanInit

end OAI
