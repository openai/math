import OAI.Computability.VPVNP.CompressorRecordsShrink
import OAI.Computability.VPVNP.PrimedStackRAMCode

/-!
# Native computation of shrinking placement rows

Scan old positions in their original order. Four reads recover the greedy color and
offset and the selected outgoing base slot's mate and shift. The resulting four
columns give the layout owner, the thickness bit, the assigned bundle's outgoing
index, and its target site. The bundle's source site is the quotient of its index by
the degree.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Public words are the residual and tag radices, degree, color-mask radix, last
color, layout bit, four input columns and four output columns. -/
def visit : List (Op 24 14) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .publicWord 3 2, .publicWord 4 3,
    .publicWord 5 4, .publicWord 6 5, .constant 22 1, .constant 23 2,
    .binary .mul 7 2 1, .binary .mod 8 0 7, .binary .div 9 0 7,
    .binary .mod 10 9 3, .binary .div 9 9 3, .binary .mod 11 9 4, .binary .div 12 9 4,
    .publicWord 13 6, .binary .add 13 13 12, .read 14 13,
    .publicWord 13 7, .binary .add 13 13 12, .read 15 13,
    .binary .mul 9 12 3, .binary .add 9 9 10,
    .publicWord 13 8, .binary .add 13 13 9, .read 16 13,
    .publicWord 13 9, .binary .add 13 13 9, .read 17 13,
    .binary .sub 14 5 14, .binary .shiftRight 19 11 14, .binary .mod 19 19 23,
    .binary .mul 15 15 1, .binary .bitXor 15 8 15,
    .binary .mod 17 17 7, .binary .bitXor 17 15 17, .binary .div 16 16 3,
    .binary .mul 16 16 7, .binary .add 16 16 17,
    .binary .mul 18 12 7, .binary .add 15 18 15, .binary .add 18 18 8,
    .binary .mul 20 15 3, .binary .add 20 20 10,
    .binary .sub 21 16 15, .binary .mul 21 6 21, .binary .add 21 15 21,
    .binary .sub 18 18 21, .binary .mul 18 19 18, .binary .add 21 21 18,
    .publicWord 13 10, .binary .add 13 13 0, .write 13 21,
    .publicWord 13 11, .binary .add 13 13 0, .write 13 19,
    .publicWord 13 12, .binary .add 13 13 0, .write 13 20,
    .publicWord 13 13, .binary .add 13 13 0, .write 13 16, .binary .add 0 0 22]

/-- Unsigned word quotient used to remove low fields when decoding a shrinking position. -/
def div (x y : Word w) := BinaryOp.div.eval x y
/-- Unsigned word remainder used to isolate a low field or a single color bit. -/
def mod (x y : Word w) := BinaryOp.mod.eval x y
/-- Bitwise exclusive OR of two words, used to apply tag offsets and lane displacements. -/
def xor (x y : Word w) := BinaryOp.bitXor.eval x y

/-- Arithmetic selection in the word ring, used with zero-or-one selectors. -/
def select (bit zeroValue oneValue : Word w) := zeroValue + bit * (oneValue - zeroValue)

@[simp] theorem select_zero (x y : Word w) : select 0 x y = x := by simp [select]
@[simp] theorem select_one (x y : Word w) : select 1 x y = y := by simp [select]

/-- The four machine words obtained by unpacking an old-position cursor in the shrinking scan. -/
structure Fields (w : ℕ) where
  /-- Base vertex index used to look up the greedy color and tag offset. -/
  base : Word w
  /-- Color mask of the old position. Its bit for the base vertex's color determines thickness. -/
  mask : Word w
  /-- Slot label selecting the outgoing base port whose mate and displacement are read. -/
  slot : Word w
  /-- The tag and residual lane packed together, with the residual lane in the least
  significant bits. -/
  low : Word w

/-- Split the old-position cursor into base vertex, color mask, slot label, and combined tag
and residual lane using the public radices. -/
def decode (p : Fin 14 → Word w) (i : Word w) : Fields w :=
  let chunk := p 1 * p 0
  let v := div i chunk
  let b := div v (p 2)
  ⟨div b (p 3), mod b (p 3), mod v (p 2), mod i chunk⟩

/-- Linear index of the outgoing base port, computed as the base vertex index times the degree
plus the slot label. -/
def baseArc (p : Fin 14 → Word w) (f : Fields w) := f.base * p 2 + f.slot

/-- Read the color and tag offset at the base vertex, then the mate and displacement at its
selected outgoing port. -/
def readColumns (p : Fin 14 → Word w) (m : Memory w) (f : Fields w) :
    Word w × Word w × Word w × Word w :=
  (m (p 6+f.base).val, m (p 7+f.base).val, m (p 8+baseArc p f).val, m (p 9+baseArc p f).val)

/-- The four entries of a shrinking placement row, parameterized by the type used to represent
their values. -/
structure Outputs (α : Type) where
  /-- Packed site to which the chosen layout assigns the old position. -/
  owner : α
  /-- Thickness flag obtained from the old position's color mask at the base vertex's greedy
  color. -/
  thick : α
  /-- Outgoing port index of the assigned bundle, encoding its source site and slot. -/
  assigned : α
  /-- Packed target site of the assigned bundle. -/
  target : α

/-- Compute the placement row from the four input columns. A thick position keeps its packed
site, while the layout bit selects the source or target for a thin position. -/
def outputs (p : Fin 14 → Word w) (m : Memory w) (i : Word w) : Outputs (Word w) :=
  let f := decode p i
  let cols := readColumns p m f
  let chunk := p 1 * p 0
  let thick := mod (BinaryOp.shiftRight.eval f.mask (p 4-cols.1)) 2
  let laneA := xor f.low (cols.2.1 * p 0)
  let A := f.base * chunk + laneA
  let B := div cols.2.2.1 (p 2) * chunk + xor laneA (mod cols.2.2.2 chunk)
  let packed := f.base * chunk + f.low
  ⟨select thick (select (p 5) A B) packed,thick,A*p 2+f.slot,B⟩

/-- The 64-event trace of one shrinking visit, including four directory reads and four output
writes at the old-position cursor. -/
def events (p : Fin 14 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let f := decode p i
  let c := readColumns p m f
  let out := outputs p m i
  List.replicate 18 .tick ++ [.read (p 6+f.base) c.1, .tick,.tick,
    .read (p 7+f.base) c.2.1,.tick,.tick,.tick,.tick,.read (p 8+baseArc p f) c.2.2.1,
    .tick,.tick,.read (p 9+baseArc p f) c.2.2.2] ++ List.replicate 23 .tick ++
    [.write (p 10+i) out.owner,.tick,.tick,.write (p 11+i) out.thick,.tick,.tick,
     .write (p 12+i) out.assigned,.tick,.tick,.write (p 13+i) out.target,.tick]

theorem visit_work (p : Fin 14 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = 64 ∧ countProbes (events p m i) = 8 := ⟨rfl,rfl⟩

/-- Write the owner, thickness, assigned port, and target to their respective output columns at
the old-position cursor. -/
def store (p : Fin 14 → Word w) (m : Memory w) (i : Word w) (out : Outputs (Word w)) : Memory w :=
  writeMemory (writeMemory (writeMemory (writeMemory m (p 10+i) out.owner)
    (p 11+i) out.thick) (p 12+i) out.assigned) (p 13+i) out.target

theorem visit_after (p : Fin 14 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = store p m i (outputs p m i) := rfl

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 8192 in
private theorem visit_trace (p : Fin 14 → Word w) (m : Memory w) (i : Word w) (rs : Regs w 24) :
    ∃ rs', trace p i visit rs m = some (events p m i, rs', store p m i (outputs p m i)) ∧
      rs' 0 = i+1 := by
  simp (config := {decide := true}) [visit, trace, Op.effect, Function.update, BinaryOp.eval,
    events, outputs, readColumns, decode, baseArc, select, div, mod, xor, store]
  repeat' apply And.intro
  all_goals rfl

/-- One deterministic burst builds all four output columns and advances the old-site cursor. -/
theorem visit_native (p : Fin 14 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 65 (M.program.start i) m [] = some ⟨events p m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := visit_trace p m i (fun _ => 0)
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

end CompressorRecords.ShrinkRAM

end VPVNP
end Computability
end OAI
