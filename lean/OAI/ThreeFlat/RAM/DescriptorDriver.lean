import OAI.ThreeFlat.RAM.DescriptorScan

namespace OAI
/-! # Instruction allocation for a bounded word-array generator -/

namespace ThreeFlat.RAM.DescriptorScan

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w d t r k : ℕ}

/-- The six contiguous driver rows follow the descriptor and precede the
continuation. Rows 0--2 load the interval and the unit increment. -/
def driverPc (d t : ℕ) (i : Fin 6) : Fin (d+(6+t)) := Fin.natAdd d (i.castAdd t)

def descriptorPc (t : ℕ) (i : Fin d) : Fin (d+(6+t)) := i.castAdd (6+t)

def tailPc (d : ℕ) (i : Fin t) : Fin (d+(6+t)) := Fin.natAdd d (Fin.natAdd 6 i)

def driverRegs (r : ℕ) : Fin 4 ↪ Fin (4+r) := Fin.castAddEmb r

def driverLabels (entry : Fin d) (exit : Fin t) : Labels (d+(6+t)) :=
  ⟨driverPc d t 3, descriptorPc t entry, driverPc d t 4, driverPc d t 5, tailPc d exit⟩

def driverRow (entry : Fin d) (exit : Fin t) (i : Fin 6) :
    Instr w (d+(6+t)) (4+r) (2+k) :=
  let R := driverRegs r
  let P := driverPc d t
  match i.val with
  | 0 => .publicWord (R 0) ((0 : Fin 2).castAdd k) (P 1)
  | 1 => .publicWord (R 1) ((1 : Fin 2).castAdd k) (P 2)
  | 2 => .constant (R 3) 1 (P 3)
  | 3 => .jumpLt (R 0) (R 1) (descriptorPc t entry) (tailPc d exit)
  | 4 => .writeExternal (R 0) (R 2) (P 5)
  | _ => .binary .add (R 0) (R 0) (R 3) (P 3)

/-- Install an actual descriptor and continuation instruction table. Only the
two interval endpoints and the routines' public words depend on the instance. -/
def assemble (entry : Fin d) (exit : Fin t)
    (desc : Fin d → Instr w (d+(6+t)) (4+r) (2+k))
    (tail : Fin t → Instr w (d+(6+t)) (4+r) (2+k))
    (start stop : Word w) (pub : Fin k → Word w) : Machine w (d+(6+t)) (4+r) (2+k) where
  entry := driverPc d t 0
  code := Fin.addCases desc (Fin.addCases (driverRow entry exit) tail)
  publicData := Fin.addCases ![start,stop] pub

variable (entry : Fin d) (exit : Fin t)
variable (desc : Fin d → Instr w (d+(6+t)) (4+r) (2+k))
variable (tail : Fin t → Instr w (d+(6+t)) (4+r) (2+k))
variable (start stop : Word w) (pub : Fin k → Word w)

@[simp] theorem assembled_driver (i : Fin 6) :
    (assemble entry exit desc tail start stop pub).code (driverPc d t i) =
      driverRow entry exit i := by simp [assemble,driverPc]

@[simp] theorem assembled_descriptor (i : Fin d) :
    (assemble entry exit desc tail start stop pub).code (descriptorPc t i) = desc i := by
  simp [assemble,descriptorPc]

@[simp] theorem assembled_tail (i : Fin t) :
    (assemble entry exit desc tail start stop pub).code (tailPc d i) = tail i := by
  simp [assemble,tailPc]

theorem driver_installed :
    Installed (assemble entry exit desc tail start stop pub) (driverRegs r) (driverLabels entry exit) := by
  constructor <;> simp only [driverLabels, assembled_driver] <;> rfl

def booted (state : Word w) : Config w (d+(6+t)) (4+r) :=
  let L := driverPc d t
  let R := driverRegs r
  let c : Config w (d+(6+t)) (4+r) := ⟨L 0,state,fun _ => 0,fun _ => 0⟩
  ((c.put (L 1) (R 0) start).put (L 2) (R 1) stop).put (L 3) (R 3) 1

theorem boot (state : Word w) (m : Memory w) :
    let M := assemble entry exit desc tail start stop pub
    advance M.program 3 (M.program.start state) m =
      some (booted (d:=d) (t:=t) (r:=r) start stop state,m) := by
  dsimp only
  simp [advance, Machine.program, assemble, driverPc, driverRow, Instr.run, booted, Config.put]

end ThreeFlat.RAM.DescriptorScan

end OAI
