import OAI.ThreeFlat.RAM.TickControlHeader
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Scanning exactly the active pair half-intervals of the current group -/

namespace ThreeFlat.RAM.TickPairHeader

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickAuxiliary
open scoped Fin.CommRing
variable {w p r k a : ℕ}

/-- One marker bit, the canonical history/final-wire register, and two equally
long packed pair halves. Every remaining physical bit is checked as padding. -/
def layout (capacity count : ℕ) (fits : 1+capacity+2*count ≤ a) : Layout a where
  wiresEnd := 1+capacity
  pairsEnd := 1+capacity+2*count
  ordered := by omega
  marker := by omega
  fits := fits

/-- The last two pointers both refer into the incoming shared auxiliary:
it already contains the complete old and new group proposals on a scan tick. -/
def values (cap n old : Word w) : Fin 4 → Word w :=
  ![cap,(cap+n)+n,old+cap,old+(cap+n)]

def selected (m : Memory w) (groupAddr counters groups : Word w) : Word w :=
  let g := m groupAddr.val
  if g < groups then m (counters+g).val else 0

def emit (P : Fin 22 → Fin p) (R : Fin 5 ↪ Fin r) (dest : Fin 4 → Word w)
    (groupAddr counters groups cap old : Word w) (exit : Fin p) : Fin 22 → Instr w p r k
  | 0 => .constant (R 0) groupAddr (P 1)
  | 1 => .readExternal (R 1) (R 0) (P 2)
  | 2 => .constant (R 0) groups (P 3)
  | 3 => .jumpLt (R 1) (R 0) (P 4) (P 7)
  | 4 => .constant (R 0) counters (P 5)
  | 5 => .binary .add (R 0) (R 0) (R 1) (P 6)
  | 6 => .readExternal (R 1) (R 0) (P 8)
  | 7 => .constant (R 1) 0 (P 8)
  | 8 => .constant (R 0) cap (P 9)
  | 9 => .binary .add (R 2) (R 0) (R 1) (P 10)
  | 10 => .binary .add (R 3) (R 2) (R 1) (P 11)
  | 11 => .constant (R 4) (dest 0) (P 12)
  | 12 => .writeExternal (R 4) (R 0) (P 13)
  | 13 => .constant (R 4) (dest 1) (P 14)
  | 14 => .writeExternal (R 4) (R 3) (P 15)
  | 15 => .constant (R 0) old (P 16)
  | 16 => .binary .add (R 2) (R 0) (R 2) (P 17)
  | 17 => .constant (R 3) (old+cap) (P 18)
  | 18 => .constant (R 4) (dest 2) (P 19)
  | 19 => .writeExternal (R 4) (R 3) (P 20)
  | 20 => .constant (R 4) (dest 3) (P 21)
  | _ => .writeExternal (R 4) (R 2) exit

set_option maxRecDepth 8192 in
set_option maxHeartbeats 500000 in
theorem advance_header (M : Machine w p r k) (P : Fin 22 → Fin p) (R : Fin 5 ↪ Fin r)
    (dest : Fin 4 → Word w) (groupAddr counters groups cap old : Word w) (exit : Fin p)
    (rom : ∀ i, M.code (P i) = emit P R dest groupAddr counters groups cap old exit i)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    ∃ n ≤ 21, ∃ d : Config w p r, d.pc = exit ∧ advance M.program n c m = some (d,
      TickControlHeader.store dest (values cap (selected m groupAddr counters groups) old) m) := by
  by_cases yes : m groupAddr.val < groups
  · refine ⟨21,by decide,?_⟩
    simp [advance,Machine.program,entry,rom,emit,Instr.run,Config.put,Function.update,
      R.injective.eq_iff,selected,yes,values,TickControlHeader.store,BinaryOp.eval,and_comm]
  · refine ⟨19,by decide,?_⟩
    simp [advance,Machine.program,entry,rom,emit,Instr.run,Config.put,Function.update,
      R.injective.eq_iff,selected,yes,values,TickControlHeader.store,BinaryOp.eval,and_comm]

theorem values_layout (capacity count old : ℕ) (fits : 1+capacity+2*count ≤ a) :
    let L := layout capacity count fits
    values (w:=w) (1+capacity : ℕ) count old =
      ![(L.wiresEnd : Word w),(L.pairsEnd : Word w),(old+L.wiresEnd : ℕ),(old+L.wiresEnd+count : ℕ)] := by
  funext i
  fin_cases i <;> simp [values,layout,Nat.cast_add,two_mul,add_assoc]

end ThreeFlat.RAM.TickPairHeader

end OAI
