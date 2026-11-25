import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace OAI
/-! # A native row of the greedy group and slot scheduler

Registers 0,1 point at the next input and output pairs. Registers 2--5 contain
the group, remaining group capacity, slot and remaining slot capacity.
Registers 6--10 supply J, B, W and the capacities of a fresh group and slot.
The two arms of each comparison execute equally many native instructions.
-/

namespace ThreeFlat.RAM.TickGreedyRow

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing ContinuationLink

variable {w p r k : ℕ}

def rows (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r) (exit : Fin p) (i : Fin 29) : Instr w p r k :=
  match i.val with
  | 0 => .constant (reg 11) 1 (pc 1)
  | 1 => .readExternal (reg 12) (reg 0) (pc 2)
  | 2 => .binary .add (reg 0) (reg 0) (reg 11) (pc 3)
  | 3 => .readExternal (reg 13) (reg 0) (pc 4)
  | 4 => .binary .add (reg 0) (reg 0) (reg 11) (pc 5)
  | 5 => .binary .mul (reg 15) (reg 7) (reg 12) (pc 6)
  | 6 => .binary .mul (reg 14) (reg 8) (reg 13) (pc 7)
  | 7 => .binary .add (reg 14) (reg 15) (reg 14) (pc 8)
  | 8 => .binary .mul (reg 14) (reg 6) (reg 14) (pc 9)
  | 9 => .jumpLt (reg 3) (reg 14) (pc 10) (pc 14)
  | 10 => .binary .add (reg 2) (reg 2) (reg 11) (pc 11)
  | 11 => .copy (reg 3) (reg 9) (pc 12)
  | 12 => .constant (reg 4) 0 (pc 13)
  | 13 => .copy (reg 5) (reg 10) (pc 18)
  | 14 => .copy (reg 2) (reg 2) (pc 15)
  | 15 => .copy (reg 3) (reg 3) (pc 16)
  | 16 => .copy (reg 4) (reg 4) (pc 17)
  | 17 => .copy (reg 5) (reg 5) (pc 18)
  | 18 => .jumpLt (reg 5) (reg 12) (pc 19) (pc 21)
  | 19 => .binary .add (reg 4) (reg 4) (reg 11) (pc 20)
  | 20 => .copy (reg 5) (reg 10) (pc 23)
  | 21 => .copy (reg 4) (reg 4) (pc 22)
  | 22 => .copy (reg 5) (reg 5) (pc 23)
  | 23 => .writeExternal (reg 1) (reg 2) (pc 24)
  | 24 => .binary .add (reg 1) (reg 1) (reg 11) (pc 25)
  | 25 => .writeExternal (reg 1) (reg 4) (pc 26)
  | 26 => .binary .add (reg 1) (reg 1) (reg 11) (pc 27)
  | 27 => .binary .sub (reg 3) (reg 3) (reg 14) (pc 28)
  | _ => .binary .sub (reg 5) (reg 5) (reg 12) exit

def block (w : ℕ) : Block w 29 16 0 where
  first := 0
  emit pc reg _ exit := rows pc reg exit

def Installed (M : Machine w p r k) (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r) (exit : Fin p) :=
  ∀ i, M.code (pc i) = rows pc reg exit i

structure State (w : ℕ) where
  group : Word w
  groupLeft : Word w
  slot : Word w
  slotLeft : Word w

def state (reg : Fin 16 ↪ Fin r) (c : Config w p r) : State w :=
  ⟨c.reg (reg 2),c.reg (reg 3),c.reg (reg 4),c.reg (reg 5)⟩

/-- Unsigned comparisons and word arithmetic, as performed by the native instructions. -/
def update (s : State w) (work pairs J B W groupCap slotCap : Word w) : State w :=
  let score := J*(B*work+W*pairs)
  let restart := s.groupLeft < score
  let group := if restart then s.group+1 else s.group
  let groupLeft := if restart then groupCap else s.groupLeft
  let slot := if restart then 0 else s.slot
  let slotLeft := if restart then slotCap else s.slotLeft
  ⟨group,groupLeft-score,if slotLeft < work then slot+1 else slot,
    (if slotLeft < work then slotCap else slotLeft)-work⟩

def scored (q : Fin p) (reg : Fin 16 ↪ Fin r) (c : Config w p r) (m : Memory w) :=
  let src := c.reg (reg 0)
  let work := m src.val
  let pairs := m (src+1).val
  let bw := c.reg (reg 7)*work
  let wp := c.reg (reg 8)*pairs
  let d := ((c.put q (reg 11) 1).put q (reg 12) work).put q (reg 0) (src+1)
  let d := ((d.put q (reg 13) pairs).put q (reg 0) (src+1+1)).put q (reg 15) bw
  ((d.put q (reg 14) wp).put q (reg 14) (bw+wp)).put q (reg 14) (c.reg (reg 6)*(bw+wp))

def grouped (q : Fin p) (reg : Fin 16 ↪ Fin r) (c : Config w p r) :=
  let reset := c.reg (reg 3) < c.reg (reg 14)
  let d := c.put q (reg 2) (if reset then c.reg (reg 2)+1 else c.reg (reg 2))
  let d := d.put q (reg 3) (if reset then c.reg (reg 9) else c.reg (reg 3))
  let d := d.put q (reg 4) (if reset then 0 else c.reg (reg 4))
  d.put q (reg 5) (if reset then c.reg (reg 10) else c.reg (reg 5))

def slotted (q : Fin p) (reg : Fin 16 ↪ Fin r) (c : Config w p r) :=
  let reset := c.reg (reg 5) < c.reg (reg 12)
  let d := c.put q (reg 4) (if reset then c.reg (reg 4)+1 else c.reg (reg 4))
  d.put q (reg 5) (if reset then c.reg (reg 10) else c.reg (reg 5))

def deducted (q : Fin p) (reg : Fin 16 ↪ Fin r) (c : Config w p r) :=
  let dst := c.reg (reg 1)
  let d := (c.put q (reg 1) (dst+1)).put q (reg 1) (dst+1+1)
  (d.put q (reg 3) (c.reg (reg 3)-c.reg (reg 14))).put q (reg 5) (c.reg (reg 5)-c.reg (reg 12))

def writePair (m : Memory w) (address group slot : Word w) : Memory w :=
  writeMemory (writeMemory m address group) (address+1) slot

variable (M : Machine w p r k) (pc : Fin 29 → Fin p) (reg : Fin 16 ↪ Fin r) (exit : Fin p)
    (rom : Installed M pc reg exit)

include rom in
theorem advance_score (c : Config w p r) (m : Memory w) (hc : c.pc = pc 0) :
    advance M.program 9 c m = some (scored (pc 9) reg c m,m) := by
  unfold Installed at rom
  simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,scored,
    Config.put,Function.update,BinaryOp.eval]

include rom in
theorem advance_group (c : Config w p r) (m : Memory w) (hc : c.pc = pc 9)
    (one : c.reg (reg 11) = 1) :
    advance M.program 5 c m = some (grouped (pc 18) reg c,m) := by
  unfold Installed at rom
  by_cases h : c.reg (reg 3) < c.reg (reg 14) <;>
    simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,grouped,
      Config.put,Function.update,BinaryOp.eval,one,h]

include rom in
theorem advance_slot (c : Config w p r) (m : Memory w) (hc : c.pc = pc 18)
    (one : c.reg (reg 11) = 1) :
    advance M.program 3 c m = some (slotted (pc 23) reg c,m) := by
  unfold Installed at rom
  by_cases h : c.reg (reg 5) < c.reg (reg 12) <;>
    simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,slotted,
      Config.put,Function.update,BinaryOp.eval,one,h]

include rom in
theorem advance_deduct (c : Config w p r) (m : Memory w) (hc : c.pc = pc 23)
    (one : c.reg (reg 11) = 1) :
    advance M.program 6 c m = some (deducted exit reg c,writePair m (c.reg (reg 1))
      (c.reg (reg 2)) (c.reg (reg 4))) := by
  unfold Installed at rom
  simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,deducted,
    Config.put,Function.update,BinaryOp.eval,one,writePair]

end ThreeFlat.RAM.TickGreedyRow

end OAI
