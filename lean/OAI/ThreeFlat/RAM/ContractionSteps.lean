import OAI.ThreeFlat.RAM.ContractionMachine

namespace OAI
/-! # Native instruction counts for a guess and a table lookup -/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
variable {F : Type*} [Semiring F] {w : ℕ}

def afterGuess (r : Registers w) (b : Word w) : Registers w :=
  Function.update (Function.update r 6 b) 0 (r 0 + 1)

theorem guess_round (code : FieldCode F w) (param : Fin 5 → Word w) (fuel : ℕ)
    (r : Registers w) (mem : Memory w) (hne : r 0 ≠ r 1) (one : r 5 = 1) :
    eval code param (fuel+5) 6 r mem =
      eval code param fuel 6 (afterGuess r 0) (writeMemory mem (r 0) 0) +
      eval code param fuel 6 (afterGuess r 1) (writeMemory mem (r 0) 1) := by
  simp [eval, mass, machine, Machine.program, config, instruction, Instr.run,
    Config.put, afterGuess, BinaryOp.eval, Function.update, hne, one]

theorem guess_done (code : FieldCode F w) (param : Fin 5 → Word w) (fuel : ℕ)
    (r : Registers w) (mem : Memory w) (heq : r 0 = r 1) :
    eval code param (fuel+1) 6 r mem = eval code param fuel 12 r mem := by
  simp [eval, mass, machine, Machine.program, config, instruction, Instr.run, heq]

theorem cells_done (code : FieldCode F w) (param : Fin 5 → Word w) (fuel : ℕ)
    (r : Registers w) (mem : Memory w) (heq : r 1 = r 2) :
    eval code param (fuel+2) 12 r mem = code.decode (r 4) := by
  simp [eval, mass, machine, Machine.program, config, instruction, Instr.run, heq,
    FieldCode.terminal]

def readBit (mem : Memory w) (ptr : Word w) : Word w := mem (mem ptr.val).val

def coefficient (mem : Memory w) (ptr : Word w) : Word w :=
  let a := readBit mem ptr
  let b := readBit mem (ptr+1)
  let c := readBit mem (ptr+1+1)
  let d := c+c+b
  mem (ptr+1+1+1+(d+d+a)).val

def afterCell (r : Registers w) (mem : Memory w) : Registers w :=
  let ptr := r 1
  let k := coefficient mem ptr
  let weight := mem (r 4 * r 3 + k + r 2).val
  fun i => match i.val with
    | 1 => ptr+1+1+1+8
    | 4 => weight
    | 6 => readBit mem ptr
    | 7 => readBit mem (ptr+1)
    | 8 => k
    | 9 => 8
    | _ => r i

/-- The register updates executed by instruction addresses 13 through 33. -/
def nativeCell (r : Registers w) (mem : Memory w) : Registers w := Id.run do
  let mut s := r
  s := Function.update s 6 (mem (s 1).val)
  s := Function.update s 6 (mem (s 6).val)
  s := Function.update s 1 (s 1 + s 5)
  s := Function.update s 7 (mem (s 1).val)
  s := Function.update s 7 (mem (s 7).val)
  s := Function.update s 1 (s 1 + s 5)
  s := Function.update s 8 (mem (s 1).val)
  s := Function.update s 8 (mem (s 8).val)
  s := Function.update s 1 (s 1 + s 5)
  s := Function.update s 8 (s 8 + s 8)
  s := Function.update s 8 (s 8 + s 7)
  s := Function.update s 8 (s 8 + s 8)
  s := Function.update s 8 (s 8 + s 6)
  s := Function.update s 8 (s 1 + s 8)
  s := Function.update s 8 (mem (s 8).val)
  s := Function.update s 9 (s 4 * s 3)
  s := Function.update s 9 (s 9 + s 8)
  s := Function.update s 9 (s 9 + s 2)
  s := Function.update s 4 (mem (s 9).val)
  s := Function.update s 9 8
  s := Function.update s 1 (s 1 + s 9)
  return s

private def withUnit (u : Word w) (r : Registers w) (mem : Memory w) : Registers w :=
  let ptr := r 1
  let a := readBit mem ptr
  let b := readBit mem (ptr+u)
  let c := readBit mem (ptr+u+u)
  let d := c+c+b
  let k := mem (ptr+u+u+u+(d+d+a)).val
  fun i => match i.val with
    | 1 => ptr+u+u+u+8
    | 4 => mem (r 4*r 3+k+r 2).val
    | 6 => a
    | 7 => b
    | 8 => k
    | 9 => 8
    | _ => r i

private theorem nativeCell_eq (r : Registers w) (mem : Memory w) :
    nativeCell r mem = withUnit (r 5) r mem := by
  funext i
  fin_cases i <;> rfl

theorem nativeCell_eq_afterCell (r : Registers w) (mem : Memory w) (one : r 5 = 1) :
    nativeCell r mem = afterCell r mem := by
  rw [nativeCell_eq, one]
  rfl

/-- A twenty-two-instruction pass performs exactly the three indirect reads,
one cell lookup and one multiplication lookup for a single record. -/
theorem cell_round (code : FieldCode F w) (param : Fin 5 → Word w) (fuel : ℕ)
    (r : Registers w) (mem : Memory w) (hne : r 1 ≠ r 2) (one : r 5 = 1) :
    eval code param (fuel+22) 12 r mem = eval code param fuel 12 (afterCell r mem) mem := by
  have start : eval code param (fuel+22) 12 r mem = eval code param (fuel+21) 13 r mem := by
    change mass code (machine param).program (fuel+21)
      {config 12 r with pc := if r 1 = r 2 then (34 : Fin 35) else 13} mem = _
    rw [ite_eq_right hne]
    rfl
  have body : eval code param (fuel+21) 13 r mem =
      eval code param fuel 12 (nativeCell r mem) mem := rfl
  rw [start, body, nativeCell_eq_afterCell r mem one]

end ThreeFlat.RAM.Contraction

end OAI
