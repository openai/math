import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Initializing the greedy scheduler's input frame from history metadata -/

namespace ThreeFlat.RAM.TickGreedySetup

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- The count and total work are read at runtime. The table bases, number of groups,
pair budget and machine size are constants of the compiled tick. -/
structure Layout where
  src : ℕ
  dst : ℕ
  countAddr : ℕ
  workAddr : ℕ
  J : ℕ
  B : ℕ
  size : ℕ

def rows (A : Layout) (P : Fin 18 → Fin p) (R : Fin 17 ↪ Fin r) (exit : Fin p)
    (i : Fin 18) : Instr w p r k :=
  match i.val with
  | 0 => .constant (R 0) (A.src : Word w) (P 1)
  | 1 => .constant (R 1) (A.dst : Word w) (P 2)
  | 2 => .constant (R 16) (A.countAddr : Word w) (P 3)
  | 3 => .readExternal (R 16) (R 16) (P 4)
  | 4 => .binary .add (R 16) (R 16) (R 16) (P 5)
  | 5 => .binary .add (R 16) (R 0) (R 16) (P 6)
  | 6 => .constant (R 6) (A.J : Word w) (P 7)
  | 7 => .constant (R 7) (A.B : Word w) (P 8)
  | 8 => .constant (R 8) (A.workAddr : Word w) (P 9)
  | 9 => .readExternal (R 8) (R 8) (P 10)
  | 10 => .binary .mul (R 9) (R 8) (R 7) (P 11)
  | 11 => .constant (R 11) 4 (P 12)
  | 12 => .binary .mul (R 9) (R 11) (R 9) (P 13)
  | 13 => .constant (R 10) ((A.size/4 : ℕ) : Word w) (P 14)
  | 14 => .constant (R 2) 0 (P 15)
  | 15 => .copy (R 3) (R 9) (P 16)
  | 16 => .constant (R 4) 0 (P 17)
  | _ => .copy (R 5) (R 10) exit

def block (w : ℕ) (A : Layout) : Block w 18 17 0 where
  first := 0
  emit P R _ exit := rows A P R exit

def pointers (A : Layout) (m : Memory w) (R : Fin 17 ↪ Fin r) (q : Fin p) (c : Config w p r) :=
  let n := m (A.countAddr : Word w).val
  let d := (c.put q (R 0) (A.src : Word w)).put q (R 1) (A.dst : Word w)
  let d := ((d.put q (R 16) (A.countAddr : Word w)).put q (R 16) n).put q (R 16) (n+n)
  d.put q (R 16) ((A.src : Word w)+(n+n))

def capacities (A : Layout) (m : Memory w) (R : Fin 17 ↪ Fin r) (q : Fin p) (c : Config w p r) :=
  let W := m (A.workAddr : Word w).val
  let gc := 4*(W*(A.B : Word w))
  let sc := ((A.size/4 : ℕ) : Word w)
  let d := (c.put q (R 6) (A.J : Word w)).put q (R 7) (A.B : Word w)
  let d := (d.put q (R 8) (A.workAddr : Word w)).put q (R 8) W
  let d := (d.put q (R 9) (W*(A.B : Word w))).put q (R 11) 4
  let d := (d.put q (R 9) gc).put q (R 10) sc
  let d := (d.put q (R 2) 0).put q (R 3) gc
  (d.put q (R 4) 0).put q (R 5) sc

def initialized (A : Layout) (m : Memory w) (R : Fin 17 ↪ Fin r) (q : Fin p) (c : Config w p r) :=
  capacities A m R q (pointers A m R q c)

/-- From arbitrary registers the prologue reads both metadata words, then installs both cursors
and capacities. The external memory is identical on entry and exit. -/
theorem advance_setup (A : Layout) (M : Machine w p r k) (P : Fin 18 ↪ Fin p) (R : Fin 17 ↪ Fin r)
    (pub : Fin 0 → Fin k) (exit : Fin p) (rom : (block w A).Installed M P R pub exit)
    (c : Config w p r) (m : Memory w) (entry : c.pc = P 0) :
    advance M.program 18 c m = some (initialized A m R exit c,m) := by
  change ∀ i, M.code (P i) = rows A P R exit i at rom
  have head : advance M.program 6 c m = some (pointers A m R (P 6) c,m) := by
    simp (config := {decide := true}) [advance,Machine.program,entry,rom,rows,Instr.run,
      Config.put,Function.update,BinaryOp.eval,pointers]
  have tail (d : Config w p r) (hd : d.pc = P 6) :
      advance M.program 12 d m = some (capacities A m R exit d,m) := by
    simp (config := {decide := true}) [advance,Machine.program,hd,rom,rows,Instr.run,
      Config.put,Function.update,BinaryOp.eval,capacities]
  exact advance_trans head (tail _ rfl)

/-- Values needed by the sweep, including its exclusive input-table bound. -/
structure Inputs (A : Layout) (n W : ℕ) (R : Fin 17 ↪ Fin r) (c : Config w p r) : Prop where
  src : c.reg (R 0) = (A.src : Word w)
  dst : c.reg (R 1) = (A.dst : Word w)
  stop : c.reg (R 16) = ((A.src+2*n : ℕ) : Word w)
  group : c.reg (R 2) = 0
  groupLeft : c.reg (R 3) = ((4*(W*A.B) : ℕ) : Word w)
  slot : c.reg (R 4) = 0
  slotLeft : c.reg (R 5) = ((A.size/4 : ℕ) : Word w)
  groups : c.reg (R 6) = (A.J : Word w)
  pairBudget : c.reg (R 7) = (A.B : Word w)
  work : c.reg (R 8) = (W : Word w)
  groupCap : c.reg (R 9) = ((4*(W*A.B) : ℕ) : Word w)
  slotCap : c.reg (R 10) = ((A.size/4 : ℕ) : Word w)

theorem initialized_inputs (A : Layout) (m : Memory w) (R : Fin 17 ↪ Fin r) (q : Fin p)
    (c : Config w p r) (n W : ℕ) (countFit : A.countAddr < 2^w) (workFit : A.workAddr < 2^w)
    (cn : m A.countAddr = (n : Word w)) (cw : m A.workAddr = (W : Word w)) :
    Inputs A n W R (initialized A m R q c) := by
  constructor <;> simp (config := {decide := true}) [initialized,pointers,capacities,Config.put,
    Function.update,Fin.val_cast_of_lt countFit,Fin.val_cast_of_lt workFit,cn,cw,two_mul]

theorem initialized_outside (A : Layout) (m : Memory w) (R : Fin 17 ↪ Fin r)
    (q : Fin p) (c : Config w p r) (i : Fin r) (h : ∀ j, i ≠ R j) :
    (initialized A m R q c).reg i = c.reg i := by
  simp [initialized,pointers,capacities,Config.put,Function.update_of_ne,h]

end ThreeFlat.RAM.TickGreedySetup

end OAI
