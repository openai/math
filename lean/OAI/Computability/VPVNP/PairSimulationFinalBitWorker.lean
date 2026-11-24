import OAI.Computability.VPVNP.PairSimulationFinalBits
import OAI.Computability.VPVNP.PairSimulationTerminalLink

/-!
# Final shared-bit worker on the eleven-operand pair interface

Each call reads the total width from the terminal header. A live ordinal
takes one choice and writes it in reverse address order. The closing ordinal
accepts with an empty choice stream, and an ordinal above the total rejects.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.FinalBits.Worker

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Base word of the terminal header shared with the stage controller. -/
abbrev header (pub : Fin 11 → Word w) : Word w := TerminalLink.header pub

/-- Instructions for computing the header address, testing the ordinal and writing one chosen bit. -/
def instruction (width : ℕ) (pc : Fin 28) : Instr width 28 5 11 :=
  match pc.val with
  | 0 => .publicWord 1 7 1
  | 1 => .constant 2 1 2
  | 2 => .binary .shiftLeft 1 2 1 3
  | 3 => .binary .mul 1 1 1 4
  | 4 => .publicWord 3 2 5
  | 5 => .binary .add 1 3 1 6
  | 6 => .constant 3 32 7
  | 7 => .binary .sub 1 1 3 8
  | 8 => .stateWord 0 9
  | 9 => .constant 3 12 10
  | 10 => .binary .add 3 1 3 11
  | 11 => .readExternal 3 3 12
  | 12 => .jumpLt 0 3 13 25
  | 13 => .constant 4 13 14
  | 14 => .binary .add 4 1 4 15
  | 15 => .readExternal 4 4 16
  | 16 => .binary .add 4 4 3 17
  | 17 => .binary .sub 4 4 0 18
  | 18 => .binary .sub 4 4 2 19
  | 19 => .choose 20 21
  | 20 => .constant 3 1 22
  | 21 => .constant 3 0 22
  | 22 => .writeExternal 4 3 23
  | 23 => .binary .add 0 0 2 24
  | 24 => .returnState 0
  | 25 => .jumpEq 0 3 26 27
  | 26 => .accept
  | _ => .reject

/-- Width-independent terminal shared-bit table with all eleven live public operands. -/
def table : Template 28 5 11 := ⟨6, 0, instruction 6⟩

theorem resize_instruction (width : ℕ) (pc : Fin 28) :
    (instruction 6 pc).resize width = instruction width pc := by fin_cases pc <;> rfl

/-- Number of wire bits published in terminal header cell 12. -/
def total (pub : Fin 11 → Word w) (m : Memory w) := m (header pub + 12).val

/-- First wire address published in terminal header cell 13. -/
def base (pub : Fin 11 → Word w) (m : Memory w) := m (header pub + 13).val

/-- Physical destination of the bit chosen at this ordinal. -/
def address (pub : Fin 11 → Word w) (m : Memory w) (i : Word w) :=
  base pub m + total pub m - i - 1

private def testEvents (pub : Fin 11 → Word w) (m : Memory w) : List (Event w) :=
  List.replicate 11 .tick ++ [.read (header pub + 12) (total pub m), .tick]

/-- Report of a data call, including both header reads and its sole external write. -/
def activeReport (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) (b : Bool) : Report w :=
  ⟨testEvents pub m ++ [.tick, .tick, .read (header pub + 13) (base pub m),
    .tick, .tick, .tick, .choice b, .tick, .write (address pub m i) (encodeBit w b), .tick],
    some (i + 1)⟩

/-- Report of the accepting call at the final ordinal. -/
def closeReport (pub : Fin 11 → Word w) (m : Memory w) : Report w :=
  ⟨testEvents pub m ++ [.tick], none⟩

@[simp] theorem active_result (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) (b : Bool) :
    (activeReport pub i m b).result = some (i + 1) := rfl

@[simp] theorem close_result (pub : Fin 11 → Word w) (m : Memory w) :
    (closeReport pub m).result = none := rfl

theorem active_cost (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) (b : Bool) :
    (activeReport pub i m b).probes = 3 ∧ (activeReport pub i m b).events.length = 23 := ⟨rfl, rfl⟩

theorem close_cost (pub : Fin 11 → Word w) (m : Memory w) :
    (closeReport pub m).probes = 1 ∧ (closeReport pub m).events.length = 14 := ⟨rfl, rfl⟩

theorem active_image (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) (b : Bool) :
    after m (activeReport pub i m b).events = writeMemory m (address pub m i) (encodeBit w b) := rfl

theorem close_image (pub : Fin 11 → Word w) (m : Memory w) :
    after m (closeReport pub m).events = m := rfl


private def tested (pub : Fin 11 → Word w) (i : Word w) (m : Memory w) : Config w 28 5 :=
  ⟨12, i, ![i, header pub, 1, total pub m, 0], fun _ => 0⟩

private theorem enter (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (bs : List Bool) (fuel : ℕ) :
    let M := table.instantiate w pub
    let pc : Fin 28 := if i < total pub m then 13 else 25
    execute M.program (fuel + 13) (M.program.start i) m bs =
      (execute M.program fuel {tested pub i m with pc := pc} m bs).map
        (fun r => ⟨testEvents pub m ++ r.events, r.result⟩) := by
  let M := table.instantiate w pub
  let span := BinaryOp.shiftLeft.eval 1 (pub 7)
  let a := M.program.start i
  let b := a.put 1 1 (pub 7)
  let c := b.put 2 2 1
  let d := c.put 3 1 span
  let e := d.put 4 1 (span * span)
  let f := e.put 5 3 (pub 2)
  let g := f.put 6 1 (pub 2 + span * span)
  let h := g.put 7 3 32
  let j := h.put 8 1 (header pub)
  let k := j.put 9 0 i
  let l := k.put 10 3 12
  let t := l.put 11 3 (header pub + 12)
  let out : Config w 28 5 := {tested pub i m with pc := if i < total pub m then 13 else 25}
  have s0 : M.program.step a = .localStep b := rfl
  have s1 : M.program.step b = .localStep c := rfl
  have s2 : M.program.step c = .localStep d := rfl
  have s3 : M.program.step d = .localStep e := rfl
  have s4 : M.program.step e = .localStep f := rfl
  have s5 : M.program.step f = .localStep g := rfl
  have s6 : M.program.step g = .localStep h := rfl
  have s7 : M.program.step h = .localStep j := rfl
  have s8 : M.program.step j = .localStep k := rfl
  have s9 : M.program.step k = .localStep l := rfl
  have s10 : M.program.step l = .localStep t := rfl
  have s11 : M.program.step t = .read (header pub + 12) (t.put 12 3) := rfl
  have regs : (t.put 12 3 (total pub m)).reg = (tested pub i m).reg := by
    funext idx
    fin_cases idx <;> rfl
  have s12 : M.program.step (t.put 12 3 (m (header pub + 12).val)) = .localStep out := by
    change CallAction.localStep
      (⟨out.pc, i, (t.put 12 3 (total pub m)).reg, fun _ => 0⟩ : Config w 28 5) = _
    rw [regs]
    rfl
  change execute M.program (fuel + 13) a m bs = (execute M.program fuel out m bs).map _
  simp only [execute, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
  cases execute M.program fuel out m bs <;> rfl

theorem active (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (hi : i < total pub m) (bs : List Bool) (extra : ℕ) :
    let M := table.instantiate w pub
    execute M.program (extra + 24) (M.program.start i) m bs =
      match bs with
      | [b] => some (activeReport pub i m b)
      | _ => none := by
  let M := table.instantiate w pub
  let a : Config w 28 5 := {tested pub i m with pc := 13}
  let b := a.put 14 4 13
  let c := b.put 15 4 (header pub + 13)
  let d := c.put 16 4 (base pub m)
  let e := d.put 17 4 (base pub m + total pub m)
  let f := e.put 18 4 (base pub m + total pub m - i)
  let g := f.put 19 4 (address pub m i)
  let choice (v : Bool) : Config w 28 5 := {g with pc := if v then 20 else 21}
  let emit (v : Bool) := g.put 22 3 (encodeBit w v)
  let advance (v : Bool) : Config w 28 5 := {emit v with pc := 23}
  let finish (v : Bool) := (advance v).put 24 0 (i + 1)
  have s13 : M.program.step a = .localStep b := rfl
  have s14 : M.program.step b = .localStep c := rfl
  have s15 : M.program.step c = .read (header pub + 13) (c.put 16 4) := rfl
  have s16 : M.program.step (c.put 16 4 (m (header pub + 13).val)) = .localStep e := rfl
  have s17 : M.program.step e = .localStep f := rfl
  have s18 : M.program.step f = .localStep g := rfl
  have s19 : M.program.step g = .branch choice := rfl
  have s20 (v : Bool) : M.program.step (choice v) = .localStep (emit v) := by cases v <;> rfl
  have s22 (v : Bool) : M.program.step (emit v) =
      .write (address pub m i) (encodeBit w v) (advance v) := rfl
  have s23 (v : Bool) : M.program.step (advance v) = .localStep (finish v) := rfl
  have s24 (v : Bool) : M.program.step (finish v) = .finish (some (i + 1)) := rfl
  dsimp only
  rw [show extra + 24 = (extra + 11) + 13 by omega, enter pub i m bs, ite_eq_left hi]
  change (execute M.program (extra + 11) a m bs).map _ = _
  cases bs with
  | nil => simp only [execute, s13, s14, s15, s16, s17, s18, s19, Option.map_none]
  | cons v tail =>
    cases tail <;> simp only [execute, s13, s14, s15, s16, s17, s18, s19, s20, s22, s23, s24] <;> rfl

theorem close (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (hi : i = total pub m) (bs : List Bool) (extra : ℕ) :
    let M := table.instantiate w pub
    execute M.program (extra + 24) (M.program.start i) m bs =
      if bs = [] then some (closeReport pub m) else none := by
  let M := table.instantiate w pub
  let a : Config w 28 5 := {tested pub i m with pc := 25}
  let b : Config w 28 5 := {a with pc := if i = total pub m then 26 else 27}
  have s25 : M.program.step a = .localStep b := rfl
  have s26 : M.program.step b = .finish none := by
    dsimp only [b]
    rw [ite_eq_left hi]
    rfl
  dsimp only
  rw [show extra + 24 = (extra + 11) + 13 by omega, enter pub i m bs, ite_eq_right (not_lt.mpr hi.ge)]
  change (execute M.program (extra + 11) a m bs).map _ = _
  cases bs <;> simp only [execute, s25, s26] <;> rfl

theorem overrun (pub : Fin 11 → Word w) (i : Word w) (m : Memory w)
    (hi : total pub m < i) (bs : List Bool) (extra : ℕ) :
    let M := table.instantiate w pub
    execute M.program (extra + 24) (M.program.start i) m bs = none := by
  let M := table.instantiate w pub
  let a : Config w 28 5 := {tested pub i m with pc := 25}
  let b : Config w 28 5 := {a with pc := if i = total pub m then 26 else 27}
  have s25 : M.program.step a = .localStep b := rfl
  have s27 : M.program.step b = .reject := by
    dsimp only [b]
    rw [ite_eq_right hi.ne']
    rfl
  dsimp only
  rw [show extra + 24 = (extra + 11) + 13 by omega, enter pub i m bs, ite_eq_right hi.not_gt]
  change (execute M.program (extra + 11) a m bs).map _ = _
  simp only [execute, s25, s27, Option.map_none]

end PairSimulation.FinalBits.Worker

end VPVNP
end Computability
end OAI
