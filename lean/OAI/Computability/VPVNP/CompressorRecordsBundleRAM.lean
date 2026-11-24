import OAI.Computability.VPVNP.CompressorRecordsShrinkRAM
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native classification of old segments in a shrinking pass

For each old outgoing port, the worker follows the actual incidence once and
reads the shrinking placement at both endpoints. It emits a bundle identifier
and a key for the segment's order within that bundle. Thick-to-thick wires use
the source owner and old outgoing slot. The other wires use the thin endpoint's
assigned bundle. The old width column is already indexed by this same port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open ShrinkRAM (div mod select)

variable {w : ℕ}

/-- Straight-line RAM operations for the old-port classifier, with 24 registers and 11 public
operands. -/
abbrev Ops := List (Op 24 11)

/-- Read one external cell at a public column base plus a register offset. -/
private def readColumn (column : Fin 11) (offset dst : Fin 24) : Ops :=
  [.publicWord 23 column, .binary .add 23 23 offset, .read dst 23]

private def writeColumn (column : Fin 11) (src : Fin 24) : Ops :=
  [.publicWord 23 column, .binary .add 23 23 0, .write 23 src]

/-- Registers 14 through 18 decode the source tag, port label, mask and
base. Registers 19 and 21 collect the thick-to-thick values, and 20 and
22 collect the selected bucket and key. -/
private def classify : Ops :=
  [.binary .mul 13 8 9,
   .binary .div 14 5 2, .binary .mod 15 14 3, .binary .div 14 14 3,
   .binary .mod 16 14 1, .binary .div 14 14 1, .binary .mod 17 14 4,
   .binary .div 18 14 4,
   .binary .mul 19 10 1, .binary .add 19 19 6,
   .binary .sub 20 12 11, .binary .mul 20 8 20, .binary .add 20 11 20,
   .publicWord 23 4, .binary .add 20 23 20,
   .binary .sub 19 19 20, .binary .mul 19 13 19, .binary .add 20 20 19,
   .binary .mul 21 17 1, .binary .add 21 21 16,
   .binary .mul 22 18 3, .binary .add 22 22 15, .binary .mul 22 22 1,
   .binary .add 22 22 6, .binary .mul 22 22 4, .binary .add 22 22 17,
   .binary .mul 22 22 1, .binary .add 22 22 16,
   .binary .sub 21 21 22, .binary .mul 21 13 21, .binary .add 22 22 21]

/-- Public words are the degree, residual radix, tag radix, mask radix,
number of external bundles, actual outgoing column, thickness, owner and
assigned columns, and the output bucket and key columns. -/
def visit : Ops :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1, .publicWord 3 2, .publicWord 4 3,
   .binary .div 5 0 1, .binary .mod 6 0 1] ++ readColumn 5 0 7 ++ [.binary .div 7 7 1] ++
  readColumn 6 5 8 ++ readColumn 6 7 9 ++ readColumn 7 5 10 ++ readColumn 8 5 11 ++
  readColumn 8 7 12 ++ classify ++ writeColumn 9 20 ++ writeColumn 10 22 ++
  [.constant 23 1, .binary .add 0 0 23]

/-- The mixed-radix source fields recovered from an old outgoing-port number to compute its
bundle and sorting key. -/
structure Digits (α : Type) where
  /-- The original base-site index remaining after the lane fields have been divided out. -/
  base : α
  /-- The source tag digit extracted after discarding the residual lane coordinate. -/
  tag : α
  /-- The outgoing port's slot within the old site. -/
  slot : α
  /-- The source mask digit used in both the thick-wire and CD sort keys. -/
  mask : α
  /-- The source slot-label digit, the least significant field of the within-bundle sorting
  key. -/
  label : α

/-- Recover the source base, tag, outgoing slot, mask, and slot label from a linear old-port
index and the public radices. -/
def decode (p : Fin 11 → Word w) (i : Word w) : Digits (Word w) :=
  let site := div i (p 0)
  let q := div site (p 1)
  let lane := div q (p 2)
  let baseMask := div lane (p 0)
  ⟨div baseMask (p 3), mod q (p 2), mod i (p 0), mod baseMask (p 3), mod lane (p 0)⟩

/-- Remove the outgoing-slot digit to obtain the source site of the current old port. -/
def sourceSite (p : Fin 11 → Word w) (i : Word w) := div i (p 0)
/-- Follow the current port's actual incidence and remove its incoming-slot digit to obtain the
target site. -/
def targetSite (p : Fin 11 → Word w) (m : Memory w) (i : Word w) := div (m (p 5+i).val) (p 0)

/-- The destination depends on the first probe. Remaining addresses depend
only on that destination, the persistent index and the public radices. -/
def readAddress (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Fin 6 → Word w :=
  let src := sourceSite p i
  let dst := targetSite p m i
  ![p 5+i, p 6+src, p 6+dst, p 7+src, p 8+src, p 8+dst]

/-- Read one of the six classification inputs for the old port, including incidence and
endpoint placement data. -/
def readValue (p : Fin 11 → Word w) (m : Memory w) (i : Word w) (t : Fin 6) :=
  m (readAddress p m i t).val

/-- Choose the thick source-port bucket when both endpoints are thick, or the assigned thin
endpoint's CD bucket otherwise. -/
def bucket (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Word w :=
  let r := readValue p m i
  let cd := p 4 + select (r 1) (r 4) (r 5)
  let dd := r 3 * p 0 + (decode p i).slot
  select (r 1 * r 2) cd dd

/-- Encode the old port's sort key, using mask and label for thick wires and the normalized
source fields for CD motifs. -/
def key (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Word w :=
  let r := readValue p m i
  let f := decode p i
  let cd := (((f.base * p 2 + f.tag) * p 0 + f.slot) * p 3 + f.mask) * p 0 + f.label
  let dd := f.mask * p 0 + f.label
  select (r 1 * r 2) cd dd

/-- Write the classified bucket and sort key into separate columns indexed by the old outgoing
port. -/
def update (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Memory w :=
  writeMemory (writeMemory m (p 9+i) (bucket p m i)) (p 10+i) (key p m i)

/-- The classifier visit's six input reads, local calculation ticks, and writes of the bucket
and key at the old port index. -/
def events (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let read (t : Fin 6) := Event.read (readAddress p m i t) (readValue p m i t)
  List.replicate 9 .tick ++ [read 0,.tick,.tick,.tick,read 1,.tick,.tick,read 2,
    .tick,.tick,read 3,.tick,.tick,read 4,.tick,.tick,read 5] ++
  List.replicate (classify.length+2) .tick ++ [.write (p 9+i) (bucket p m i),
    .tick,.tick,.write (p 10+i) (key p m i),.tick,.tick]

theorem events_after (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    after m (events p m i) = update p m i := rfl

theorem events_work (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    (events p m i).length = visit.length ∧ countProbes (events p m i) = 8 := ⟨rfl,rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem visit_trace (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    ∃ rs, trace p i visit (fun _ ↦ 0) m = some (events p m i,rs,update p m i) ∧ rs 0 = i+1 := by
  simp (config := {decide := true}) [visit, classify, readColumn, writeColumn, events, update, bucket,
    key, decode, readValue, readAddress, sourceSite, targetSite, select, div, mod, trace, Op.effect,
    BinaryOp.eval, Function.update, List.replicate_succ]
  rfl

/-- The actual interpreter returns the next source port and the six reads
followed by two writes, with fresh private registers on every call. -/
theorem visit_native (p : Fin 11 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program (1 + visit.length) (M.program.start i) m [] =
      some ⟨events p m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := visit_trace p m i
  let M := (template visit 0).instantiate w p
  change execute M.program (1 + visit.length) ⟨M.entry, i, fun _ ↦ 0, fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hr]

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
