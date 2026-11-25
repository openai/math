import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock
import OAI.ThreeFlat.RAM.WordSegment
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace OAI
/-! # Native grouped interval cursor for a chunk map

Each four-word descriptor stores the group, half-open interval endpoints and
packed offset. Input registers 0 through 5 hold the descriptor cursor, its
exclusive end, chunk start, chunk end, map base and selected group respectively.
-/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink Fin.CommRing

variable {w p r k : ℕ}

/-- Register 6 is one, 7--10 hold the descriptor, 11--12 delimit the clipped
interval, and 13--14 are the evolving output address and packed payload. -/
def rows (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p) (i : Fin 27) : Instr w p r k :=
  match i.val with
  | 0 => .constant (reg 6) 1 (pc 1)
  | 1 => .jumpLt (reg 0) (reg 1) (pc 2) exit
  | 2 => .readExternal (reg 7) (reg 0) (pc 3)
  | 3 => .binary .add (reg 0) (reg 0) (reg 6) (pc 4)
  | 4 => .readExternal (reg 8) (reg 0) (pc 5)
  | 5 => .binary .add (reg 0) (reg 0) (reg 6) (pc 6)
  | 6 => .readExternal (reg 9) (reg 0) (pc 7)
  | 7 => .binary .add (reg 0) (reg 0) (reg 6) (pc 8)
  | 8 => .readExternal (reg 10) (reg 0) (pc 9)
  | 9 => .binary .add (reg 0) (reg 0) (reg 6) (pc 10)
  | 10 => .jumpEq (reg 7) (reg 5) (pc 11) (pc 1)
  | 11 => .jumpLt (reg 8) (reg 2) (pc 12) (pc 13)
  | 12 => .copy (reg 11) (reg 2) (pc 14)
  | 13 => .copy (reg 11) (reg 8) (pc 14)
  | 14 => .jumpLt (reg 9) (reg 3) (pc 15) (pc 16)
  | 15 => .copy (reg 12) (reg 9) (pc 17)
  | 16 => .copy (reg 12) (reg 3) (pc 17)
  | 17 => .binary .sub (reg 13) (reg 11) (reg 2) (pc 18)
  | 18 => .binary .add (reg 13) (reg 4) (reg 13) (pc 19)
  | 19 => .binary .sub (reg 14) (reg 11) (reg 8) (pc 20)
  | 20 => .binary .add (reg 14) (reg 14) (reg 10) (pc 21)
  | 21 => .binary .add (reg 14) (reg 14) (reg 6) (pc 22)
  | 22 => .jumpLt (reg 11) (reg 12) (pc 23) (pc 1)
  | 23 => .writeExternal (reg 13) (reg 14) (pc 24)
  | 24 => .binary .add (reg 13) (reg 13) (reg 6) (pc 25)
  | 25 => .binary .add (reg 14) (reg 14) (reg 6) (pc 26)
  | _ => .binary .add (reg 11) (reg 11) (reg 6) (pc 22)

def block (w : ℕ) : Block w 27 15 0 where
  first := 0
  emit pc reg _ exit := rows pc reg exit

def Installed (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p) :=
  ∀ i, M.code (pc i) = rows pc reg exit i

theorem block_rows (M : Machine w p r k) (pc : Fin 27 ↪ Fin p) (reg : Fin 15 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (h : (block w).Installed M pc reg pub exit) :
    Installed M pc reg exit := h

def fetchWord (q : Fin p) (reg : Fin 15 ↪ Fin r) (mem : Memory w) (d : Fin 15)
    (c : Config w p r) : Config w p r :=
  let ptr := c.reg (reg 0)
  (c.put q (reg d) (mem ptr.val)).put q (reg 0) (ptr+1)

def fetched (q : Fin p) (reg : Fin 15 ↪ Fin r) (mem : Memory w) (c : Config w p r) :=
  fetchWord q reg mem 10 (fetchWord q reg mem 9 (fetchWord q reg mem 8 (fetchWord q reg mem 7 c)))

variable (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p)
    (rom : Installed M pc reg exit)

include rom in
theorem advance_init (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 0) :
    advance M.program 1 c mem = some (c.put (pc 1) (reg 6) 1,mem) := by
  unfold Installed at rom
  simp [advance, Machine.program, hc, rom, rows, Instr.run]

include rom in
theorem advance_done (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 1)
    (done : ¬c.reg (reg 0) < c.reg (reg 1)) :
    advance M.program 1 c mem = some ({c with pc := exit},mem) := by
  unfold Installed at rom
  simp [advance, Machine.program, hc, rom, rows, Instr.run, done]

include rom in
theorem advance_fetch (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 1)
    (more : c.reg (reg 0) < c.reg (reg 1)) (one : c.reg (reg 6) = 1) :
    advance M.program 9 c mem = some (fetched (pc 10) reg mem c,mem) := by
  unfold Installed at rom
  simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,more,one,
    fetched,fetchWord,Config.put,Function.update,BinaryOp.eval]

include rom in
theorem advance_group (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 10) :
    advance M.program 1 c mem =
      some ({c with pc := if c.reg (reg 7) = c.reg (reg 5) then pc 11 else pc 1},mem) := by
  unfold Installed at rom
  simp [advance,Machine.program,hc,rom,rows,Instr.run]

def prepared (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r) : Config w p r :=
  let lo := max (c.reg (reg 8)) (c.reg (reg 2))
  let hi := min (c.reg (reg 9)) (c.reg (reg 3))
  let dst := lo - c.reg (reg 2)
  let tag := lo - c.reg (reg 8)
  let b := (c.put q (reg 11) lo).put q (reg 12) hi
  let b := (b.put q (reg 13) dst).put q (reg 13) (c.reg (reg 4) + dst)
  let b := (b.put q (reg 14) tag).put q (reg 14) (tag + c.reg (reg 10))
  b.put q (reg 14) (tag + c.reg (reg 10) + 1)

include rom in
theorem advance_prepare (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 11)
    (one : c.reg (reg 6) = 1) :
    advance M.program 9 c mem = some (prepared (pc 22) reg c,mem) := by
  unfold Installed at rom
  by_cases a : c.reg (reg 8) < c.reg (reg 2) <;> by_cases b : c.reg (reg 9) < c.reg (reg 3)
  all_goals simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,
    prepared,Config.put,Function.update,BinaryOp.eval,one,a,b,
    max_def_lt,min_def_lt]

def wrote (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r) : Config w p r :=
  ((c.put q (reg 13) (c.reg (reg 13)+1)).put q (reg 14) (c.reg (reg 14)+1)).put
    q (reg 11) (c.reg (reg 11)+1)

include rom in
theorem advance_write (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 22)
    (more : c.reg (reg 11) < c.reg (reg 12)) (one : c.reg (reg 6) = 1) :
    advance M.program 5 c mem =
      some (wrote (pc 22) reg c,writeMemory mem (c.reg (reg 13)) (c.reg (reg 14))) := by
  unfold Installed at rom
  simp (config := {decide := true}) [advance,Machine.program,hc,rom,rows,Instr.run,more,one,
    wrote,Config.put,Function.update,BinaryOp.eval]

include rom in
theorem advance_write_done (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 22)
    (done : ¬c.reg (reg 11) < c.reg (reg 12)) :
    advance M.program 1 c mem = some ({c with pc := pc 1},mem) := by
  unfold Installed at rom
  simp [advance,Machine.program,hc,rom,rows,Instr.run,done]

end ThreeFlat.RAM.TickIntervalCursor

end OAI
