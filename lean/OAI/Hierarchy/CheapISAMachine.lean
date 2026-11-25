import OAI.Hierarchy.CheapISABanks
import OAI.Hierarchy.TaggedShorterCheapCPU
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI
/-! # A fixed native instruction decoder for the bounded arithmetic RAM -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

/-- Tag, literal, two register addresses, destination address, and two continuations.
Public operands are resolved in the original immutable table when writing the seven columns. -/
def fields {w p r k : ℕ} (pub : Fin k → Word w) (instr : Instr w p r k) :
    Fin 7 → Word (width w) :=
  let row (tag : ℕ) (value : Word (width w)) (x y dst yes no : ℕ) : Fin 7 → Word (width w) :=
    ![(tag : Word _), value, (x : Word _), (y : Word _), (dst : Word _),
      (yes : Word _), (no : Word _)]
  match instr with
  | .constant d v c => row 0 (wide v) 0 0 (regAddr p d) c.val 0
  | .publicWord d j c => row 0 (wide (pub j)) 0 0 (regAddr p d) c.val 0
  | .stateWord d c => row 1 0 0 0 (regAddr p d) c.val 0
  | .copy d x c => row 2 0 (regAddr p x) 0 (regAddr p d) c.val 0
  | .binary op d x y c =>
      row (match op with | .add => 3 | .sub => 4 | .bitAnd => 5 | _ => 12)
        0 (regAddr p x) (regAddr p y) (regAddr p d) c.val 0
  | .jumpEq x y a b => row 6 0 (regAddr p x) (regAddr p y) 0 a.val b.val
  | .jumpLt x y a b => row 7 0 (regAddr p x) (regAddr p y) 0 a.val b.val
  | .readExternal d x c => row 8 0 (regAddr p x) 0 (regAddr p d) c.val 0
  | .writeExternal x y c => row 9 0 (regAddr p x) (regAddr p y) 0 c.val 0
  | .returnState x => row 10 0 (regAddr p x) 0 0 0 0
  | .accept => row 11 0 0 0 0 0 0
  | _ => row 12 0 0 0 0 0 0

def ROM {w p r k : ℕ} (M : Machine w p r k) (pc : Fin p) := fields M.publicData (M.code pc)

/-- Registers 0, 1…7, 8/9, 10, 11 and 12 hold the virtual PC, instruction row,
two operand values, address scratch, result and low-word mask. Only external
RAM is shared between successive simulated instructions. -/
def code (w p r : ℕ) (entry : Fin p) (pc : Fin 72) : Instr (width w) 72 13 0 :=
  match pc.val with
  | 0 => .constant 0 (entry.val : Word _) 1
  | 1 => .constant 10 (columnBase p 0 : Word _) 2
  | 2 => .binary .add 10 10 0 3
  | 3 => .readExternal 1 10 4
  | 4 => .constant 10 (columnBase p 1 : Word _) 5
  | 5 => .binary .add 10 10 0 6
  | 6 => .readExternal 2 10 7
  | 7 => .constant 10 (columnBase p 2 : Word _) 8
  | 8 => .binary .add 10 10 0 9
  | 9 => .readExternal 3 10 10
  | 10 => .constant 10 (columnBase p 3 : Word _) 11
  | 11 => .binary .add 10 10 0 12
  | 12 => .readExternal 4 10 13
  | 13 => .constant 10 (columnBase p 4 : Word _) 14
  | 14 => .binary .add 10 10 0 15
  | 15 => .readExternal 5 10 16
  | 16 => .constant 10 (columnBase p 5 : Word _) 17
  | 17 => .binary .add 10 10 0 18
  | 18 => .readExternal 6 10 19
  | 19 => .constant 10 (columnBase p 6 : Word _) 20
  | 20 => .binary .add 10 10 0 21
  | 21 => .readExternal 7 10 22
  | 22 => .readExternal 8 3 23
  | 23 => .readExternal 9 4 24
  | 24 => .constant 10 0 25
  | 25 => .jumpEq 1 10 49 26
  | 26 => .constant 10 1 27
  | 27 => .jumpEq 1 10 50 28
  | 28 => .constant 10 2 29
  | 29 => .jumpEq 1 10 51 30
  | 30 => .constant 10 3 31
  | 31 => .jumpEq 1 10 52 32
  | 32 => .constant 10 4 33
  | 33 => .jumpEq 1 10 53 34
  | 34 => .constant 10 5 35
  | 35 => .jumpEq 1 10 54 36
  | 36 => .constant 10 6 37
  | 37 => .jumpEq 1 10 55 38
  | 38 => .constant 10 7 39
  | 39 => .jumpEq 1 10 56 40
  | 40 => .constant 10 8 41
  | 41 => .jumpEq 1 10 57 42
  | 42 => .constant 10 9 43
  | 43 => .jumpEq 1 10 60 44
  | 44 => .constant 10 10 45
  | 45 => .jumpEq 1 10 63 46
  | 46 => .constant 10 11 47
  | 47 => .jumpEq 1 10 64 48
  | 49 => .copy 11 2 68
  | 50 => .stateWord 11 68
  | 51 => .copy 11 8 68
  | 52 => .binary .add 11 8 9 67
  | 53 => .binary .sub 11 8 9 67
  | 54 => .binary .bitAnd 11 8 9 68
  | 55 => .jumpEq 8 9 70 71
  | 56 => .jumpLt 8 9 70 71
  | 57 => .constant 10 (dataBase p r : Word _) 58
  | 58 => .binary .add 10 10 8 59
  | 59 => .readExternal 11 10 68
  | 60 => .constant 10 (dataBase p r : Word _) 61
  | 61 => .binary .add 10 10 8 62
  | 62 => .writeExternal 10 9 70
  | 63 => .returnState 8
  | 64 => .accept
  | 67 => .constant 12 (mask w) 69
  | 68 => .writeExternal 5 11 70
  | 69 => .binary .bitAnd 11 11 12 68
  | 70 => .copy 0 6 1
  | 71 => .copy 0 7 1
  | _ => .reject

def machine (w p r : ℕ) (entry : Fin p) : Machine (width w) 72 13 0 where
  entry := 0
  code := code w p r entry
  publicData := Fin.elim0

theorem machine_cheap (w p r : ℕ) (entry : Fin p) :
    ∀ pc, TaggedShorterCheapCPU.Cheap ((machine w p r entry).code pc) := by
  intro pc
  fin_cases pc <;> trivial

variable {w p r k : ℕ}

/-- At a virtual instruction boundary the only designated physical register is the
virtual program counter. All original registers are in the contiguous register bank. -/
structure Rel (M : Machine w p r k) (c : Config w p r) (m : Memory w)
    (d : Config (width w) 72 13) (n : Memory (width w)) : Prop where
  atFetch : d.pc = 1
  virtualPC : d.reg 0 = (c.pc.val : Word (width w))
  persistent : d.persistent = wide c.persistent
  banks : Banks (ROM M) c.reg m n

/-- The prefetched instruction operands at label 24. The two loads also take
place for immediate and halt instructions, using address zero for unused ports. -/
structure Fetched (M : Machine w p r k) (c : Config w p r) (m : Memory w)
    (d : Config (width w) 72 13) (n : Memory (width w)) : Prop where
  atDecode : d.pc = 24
  persistent : d.persistent = wide c.persistent
  banks : Banks (ROM M) c.reg m n
  field (f : Fin 7) : d.reg ⟨f.val+1,by omega⟩ = ROM M c.pc f
  left : d.reg 8 = n (ROM M c.pc 2).val
  right : d.reg 9 = n (ROM M c.pc 3).val

end Hierarchy.CheapISA

end OAI
