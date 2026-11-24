import OAI.Computability.VPVNP.CompressorSliceRAM

/-!
# Indexing the copy records incident to each field

In the Appendix E interval scan, each candidate has a three-word output frame.
A second scan reads the length from this frame. For a positive length it appends
the candidate number to the adjacency lists of both fields. Rows are allocated
with one possible reference per opposite field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM BurstRAM.PrivateRAM

variable {w : ℕ}

/-- The seven public words are the new field count, the old field count, the output
frame base, and the count and reference bases for the old and new fields in order. -/
def adjFrameLength (pub : Fin 7 → Word w) (k : Word w) : Word w := pub 2 + 3 * k + 2

/-- Address of the number of retained slice frames for source field `i`. -/
def adjOldCount (pub : Fin 7 → Word w) (i : Word w) : Word w := pub 3 + i

/-- First reference cell in the adjacency row for source field `i`. -/
def adjOldRow (pub : Fin 7 → Word w) (i : Word w) : Word w := pub 4 + i * pub 0

/-- Address of the number of retained slice frames for target field `j`. -/
def adjNewCount (pub : Fin 7 → Word w) (j : Word w) : Word w := pub 5 + j

/-- First reference cell in the adjacency row for target field `j`. -/
def adjNewRow (pub : Fin 7 → Word w) (j : Word w) : Word w := pub 6 + j * pub 1

/-- Write one candidate number at the current end of a row and increment its count. -/
def adjAppend (mem : Memory w) (count row value : Word w) : Memory w :=
  writeMemory (writeMemory mem (row + mem count.val) value) count (mem count.val + 1)

/-- Append the frame ordinal to both endpoint rows exactly when its recorded length is
positive. -/
def adjUpdate (pub : Fin 7 → Word w) (mem : Memory w) (k : Word w) : Memory w :=
  if mem (adjFrameLength pub k).val = 0 then mem else
    adjAppend (adjAppend mem (adjOldCount pub (k / pub 0)) (adjOldRow pub (k / pub 0)) k)
      (adjNewCount pub (k % pub 0)) (adjNewRow pub (k % pub 0)) k

/-- One fresh call reads the frame length, handles both nonempty adjacency writes
and returns the next candidate number. Register eight is zero at call entry. -/
def adjTemplate : Template 36 9 7 where
  literalWidth := 2
  entry := 0
  code pc := match pc.val with
    | 0 => .stateWord 0 1
    | 1 => .constant 1 1 2
    | 2 => .constant 2 3 3
    | 3 => .binary .mul 2 2 0 4
    | 4 => .publicWord 3 2 5
    | 5 => .binary .add 3 3 2 6
    | 6 => .constant 2 2 7
    | 7 => .binary .add 3 3 2 8
    | 8 => .readExternal 4 3 9
    | 9 => .jumpEq 4 8 34 10
    | 10 => .publicWord 2 0 11
    | 11 => .binary .div 3 0 2 12
    | 12 => .binary .mod 4 0 2 13
    | 13 => .publicWord 5 3 14
    | 14 => .binary .add 5 5 3 15
    | 15 => .readExternal 6 5 16
    | 16 => .binary .mul 3 3 2 17
    | 17 => .publicWord 7 4 18
    | 18 => .binary .add 7 7 3 19
    | 19 => .binary .add 7 7 6 20
    | 20 => .writeExternal 7 0 21
    | 21 => .binary .add 6 6 1 22
    | 22 => .writeExternal 5 6 23
    | 23 => .publicWord 2 1 24
    | 24 => .publicWord 5 5 25
    | 25 => .binary .add 5 5 4 26
    | 26 => .readExternal 6 5 27
    | 27 => .binary .mul 4 4 2 28
    | 28 => .publicWord 7 6 29
    | 29 => .binary .add 7 7 4 30
    | 30 => .binary .add 7 7 6 31
    | 31 => .writeExternal 7 0 32
    | 32 => .binary .add 6 6 1 33
    | 33 => .writeExternal 5 6 34
    | 34 => .binary .add 0 0 1 35
    | _ => .returnState 0

private def appendEvents (mem : Memory w) (count row k : Word w) : List (Event w) :=
  let size := mem count.val
  [.read count size, .tick, .tick, .tick, .tick, .write (row + size) k, .tick,
    .write count (size + 1)]

/-- The target row's size is read from memory after the source row's two writes. -/
def adjEvents (pub : Fin 7 → Word w) (mem : Memory w) (k : Word w) : List (Event w) :=
  let a := adjFrameLength pub k
  let length := mem a.val
  let i := k / pub 0
  let j := k % pub 0
  let updated := adjAppend mem (adjOldCount pub i) (adjOldRow pub i) k
  List.replicate 8 .tick ++ [.read a length, .tick] ++
    (if length = 0 then [] else
      List.replicate 5 .tick ++ appendEvents mem (adjOldCount pub i) (adjOldRow pub i) k ++
      List.replicate 3 .tick ++ appendEvents updated (adjNewCount pub j) (adjNewRow pub j) k) ++
    [.tick]

theorem adjEvents_after (pub : Fin 7 → Word w) (mem : Memory w) (k : Word w) :
    after mem (adjEvents pub mem k) = adjUpdate pub mem k := by
  by_cases h : mem (adjFrameLength pub k).val = 0 <;>
    simp only [adjEvents, adjUpdate, h, ↓reduceIte] <;> rfl

theorem adjEvents_work (pub : Fin 7 → Word w) (mem : Memory w) (k : Word w) :
    countProbes (adjEvents pub mem k) = (if mem (adjFrameLength pub k).val = 0 then 1 else 7) ∧
      (adjEvents pub mem k).length + 1 = (if mem (adjFrameLength pub k).val = 0 then 12 else 36) := by
  by_cases h : mem (adjFrameLength pub k).val = 0 <;>
    simp only [adjEvents, h, ↓reduceIte] <;> exact ⟨rfl,rfl⟩

open Fin.NatCast

private theorem divWord (x y : Word w) : ((x.val / y.val : ℕ) : Word w) = x / y :=
  Fin.ext (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) x.isLt))

private theorem modWord (x y : Word w) : ((x.val % y.val : ℕ) : Word w) = x % y :=
  Fin.ext (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le ..) x.isLt))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem adjVisit_native (pub : Fin 7 → Word w) (mem : Memory w) (k : Word w) :
    let M := adjTemplate.instantiate w pub
    execute M.program 36 (M.program.start k) mem [] = some ⟨adjEvents pub mem k, some (k + 1)⟩ := by
  dsimp only
  by_cases h : mem (adjFrameLength pub k).val = 0 <;>
    simp only [adjEvents, h, ↓reduceIte] <;>
    simp only [adjFrameLength] at h <;>
    simp (config := {decide := true}) [h, adjTemplate, Template.instantiate, Machine.program,
      execute, Instr.resize, Instr.run, Config.put, BinaryOp.eval, Function.update,
      adjFrameLength, adjOldCount, adjOldRow, adjNewCount, adjNewRow, adjAppend,
      appendEvents, Report.prepend, divWord, modWord]

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI
