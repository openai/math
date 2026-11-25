import OAI.ThreeFlat.RAM.Weighted
import Mathlib.Tactic

namespace OAI
/-! # A word RAM for contraction of trivalent bit networks

The five public words are the bases of the hidden bits, cell records and field
multiplication table, the field cardinality, and the code of the unit scalar.
Each eleven-word cell record gives three bit addresses followed by its eight
coefficients in little-endian bit order.
-/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

/-- Register 0 scans the guesses, 1 scans the cell records, 2 and 3 hold the
multiplication table base and stride, and 4 accumulates the path weight. -/
def instruction {w : ℕ} (pc : Fin 35) : Instr w 35 10 5 :=
  match pc.val with
  | 0 => .publicWord 0 0 1
  | 1 => .publicWord 1 1 2
  | 2 => .publicWord 2 2 3
  | 3 => .publicWord 3 3 4
  | 4 => .publicWord 4 4 5
  | 5 => .constant 5 1 6
  | 6 => .jumpEq 0 1 12 7
  | 7 => .choose 9 8
  | 8 => .constant 6 0 10
  | 9 => .constant 6 1 10
  | 10 => .writeExternal 0 6 11
  | 11 => .binary .add 0 0 5 6
  | 12 => .jumpEq 1 2 34 13
  | 13 => .readExternal 6 1 14
  | 14 => .readExternal 6 6 15
  | 15 => .binary .add 1 1 5 16
  | 16 => .readExternal 7 1 17
  | 17 => .readExternal 7 7 18
  | 18 => .binary .add 1 1 5 19
  | 19 => .readExternal 8 1 20
  | 20 => .readExternal 8 8 21
  | 21 => .binary .add 1 1 5 22
  | 22 => .binary .add 8 8 8 23
  | 23 => .binary .add 8 8 7 24
  | 24 => .binary .add 8 8 8 25
  | 25 => .binary .add 8 8 6 26
  | 26 => .binary .add 8 1 8 27
  | 27 => .readExternal 8 8 28
  | 28 => .binary .mul 9 4 3 29
  | 29 => .binary .add 9 9 8 30
  | 30 => .binary .add 9 9 2 31
  | 31 => .readExternal 4 9 32
  | 32 => .constant 9 8 33
  | 33 => .binary .add 1 1 9 12
  | _ => .returnState 4

def machine {w : ℕ} (param : Fin 5 → Word w) : Machine w 35 10 5 :=
  ⟨0, instruction, param⟩

abbrev Registers (w : ℕ) := Fin 10 → Word w

def config {w : ℕ} (pc : Fin 35) (reg : Registers w) : Config w 35 10 :=
  ⟨pc, 0, reg, fun _ => 0⟩

variable {F : Type*} [Semiring F] {w : ℕ}

abbrev eval (code : FieldCode F w) (param : Fin 5 → Word w) (fuel : ℕ)
    (pc : Fin 35) (reg : Registers w) (mem : Memory w) : F :=
  mass code (machine param).program fuel (config pc reg) mem

def initialized {w : ℕ} (param : Fin 5 → Word w) : Registers w :=
  fun i => match i.val with
    | 0 => param 0
    | 1 => param 1
    | 2 => param 2
    | 3 => param 3
    | 4 => param 4
    | 5 => 1
    | _ => 0

theorem startup_regs (param : Fin 5 → Word w) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ : Fin 10 => (0 : Word w))
        0 (param 0)) 1 (param 1)) 2 (param 2)) 3 (param 3)) 4 (param 4)) 5 1 =
      initialized param := by
  funext i
  fin_cases i <;> simp [Function.update, initialized]

theorem startup (code : FieldCode F w) (param : Fin 5 → Word w)
    (fuel : ℕ) (mem : Memory w) :
    value code (machine param) (fuel + 6) 0 mem = eval code param fuel 6 (initialized param) mem := by
  change _ = mass _ _ _ _ _
  simp [value, mass, machine, instruction, Machine.program, Instr.run, Config.put,
    config, startup_regs]

end ThreeFlat.RAM.Contraction

end OAI
