import OAI.Computability.BorderVNP.DiagonalExternalFragmentStream
import OAI.Computability.BorderVNP.CubeHostScatterSetup
import OAI.Computability.BorderVNP.FragmentBucketLoop

/-! # Native emission of the sparse external argument directory

Two passes emit the crossing cable ends, in source order and then destination
order. A third pass emits the populated seven-word data deliveries whose
destinations are in the supplied bank. Each output names the logical offset
and the physical source. Word 29 of the indirect control frame receives the
number of emitted quadruples.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Cube.HostScatter Diagonal.ExternalSew.Fragments VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The physical lengths and pointers used by the sparse fragment scan. -/
structure Layout where
  /-- Host-scatter layout used to read both ends of each cable. -/
  host : Cube.HostScatter.Layout
  /-- Base address of the seven-word data-delivery rows. -/
  deliveries : ℕ
  /-- Number of data-delivery rows to examine. -/
  count : ℕ
  /-- Number of cells with supplied-width and cell-bank entries. -/
  cells : ℕ
  /-- Base address of the indirect frame holding the output pointer and emitted row count. -/
  control : ℕ
  /-- Base address for the four-word records emitted by the cable and data passes. -/
  quads : ℕ

/-- Decode the addresses used by the native program. -/
def Layout.fromFrame (head : ℕ) (m : ℕ → ℕ) : Layout :=
  ⟨Cube.HostScatter.Layout.fromFrame head m,m (head+8),m (head+9),m (head+11),m (head+92),m (m (head+92)+28)⟩

/-- First supplied-width word after the paired cable offsets. -/
def Layout.supplied (l : Layout) := l.host.relative+2*l.host.count

/-- Decode one seven-word data row in the public directory. -/
def Layout.row (l : Layout) (m : ℕ → ℕ) (i : ℕ) : Packing.Directory.Row :=
  let p := l.deliveries+7*i
  ⟨m p,m (p+1),m (p+2),m (p+3),m (p+4),m (p+5),m (p+6)⟩

/-- Supply intervals and cell-bank base addresses come from the actual geometry. -/
def Layout.liveRow (l : Layout) (m : ℕ → ℕ) (i : ℕ) :=
  live (fun c => m (l.supplied+c)) (fun c => m (l.host.cells+2*c+1)) (l.row m i)

/-- Source arrays that must survive while the compact result is appended. -/
def Layout.Input (l : Layout) (a : ℕ) : Prop :=
  (l.host.cables ≤ a ∧ a < l.host.cables+3*l.host.count) ∨
  (l.deliveries ≤ a ∧ a < l.deliveries+7*l.count) ∨
  (l.host.relative ≤ a ∧ a < l.supplied+l.cells) ∨
  (l.host.cells ≤ a ∧ a < l.host.cells+2*l.cells)

/-- Exact finite allocation and source-row constraints. -/
structure Layout.Fits (l : Layout) (w : ℕ) (m : ℕ → ℕ) : Prop where
  head : l.host.frame+92 < 2^w
  control : l.control+29 < 2^w
  cableEnd : l.host.cables+3*l.host.count ≤ 2^w
  dataEnd : l.deliveries+7*l.count ≤ 2^w
  relativeEnd : l.supplied+l.cells < 2^w
  cellEnd : l.host.cells+2*l.cells ≤ 2^w
  quadEnd : l.quads+4*(2*l.host.count+l.count) ≤ 2^w
  cableCell : ∀ i < l.host.count, ∀ side, l.host.width m i ≠ 0 → l.host.cell m i false ≠ l.host.cell m i true →
    l.host.cell m i side < l.cells
  dataCell : ∀ i < l.count, (l.row m i).cell < l.cells
  cableSource : ∀ i < l.host.count, ∀ side, l.host.width m i ≠ 0 → l.host.cell m i false ≠ l.host.cell m i true →
    l.host.dest m i side < 2^w
  dataSource : ∀ i < l.count, ∀ q, l.liveRow m i = some q → q.source < 2^w
  outside : ∀ a, l.Input a → a < l.quads ∨ l.quads+4*(2*l.host.count+l.count) ≤ a
  controlOutside : l.control+29 < l.quads ∨ l.quads+4*(2*l.host.count+l.count) ≤ l.control+29

/-- Bind the actual frame and indirect control words once. Register 14 counts
occupied output records, 15 is the local pass index. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 3,.constant 4 4,.constant 5 7,
  readFrame 6 62 63 6,readFrame 7 62 63 7,readFrame 8 62 63 8,readFrame 9 62 63 9,
  readFrame 10 62 63 87,readFrame 11 62 63 72,readFrame 12 62 63 92,
  .constant 25 28,.binary .add 25 12 25,.load 13 25,.copy 14 0,
  .binary .mul 16 2 7,.binary .add 16 10 16]

/-- Store one accepted interval and advance the occupied count. -/
def appendQuad : Code := .block [
  .binary .mul 24 2 20,.binary .add 24 11 24,.binary .add 24 24 1,.load 24 24,.binary .add 24 24 21,
  .binary .mul 25 4 14,.binary .add 25 13 25,
  .store 25 20,.binary .add 25 25 1,.store 25 21,.binary .add 25 25 1,.store 25 24,
  .binary .add 25 25 1,.store 25 22,.binary .add 14 14 1]

/-- Read the width, both cells, and the public within-cell offset for the
selected endpoint. Internal cables and width-zero padding produce no output. -/
def cableStep (side : Bool) : Code := .block [
  .binary .mul 26 3 15,.binary .add 26 6 26,.load 20 26,.binary .add 26 26 1,.load 27 26,
  .binary .add 26 26 1,.load 22 26,
  .ifEq 20 27 .nop (.ifEq 22 0 .nop (.block [
    (if side then .copy 20 27 else .nop),.binary .mul 26 2 15,.binary .add 26 10 26,
    (if side then .binary .add 26 26 1 else .nop),.load 21 26,appendQuad])),
  .binary .add 15 15 1]

/-- Check whether a populated row begins in the actual cell's supplied bank.
Private site tapes lie beyond it. -/
def dataStep : Code := .block [
  .binary .mul 26 5 15,.binary .add 26 8 26,.binary .add 26 26 4,.load 20 26,
  .binary .add 26 26 1,.load 21 26,.binary .add 26 26 1,.load 22 26,
  .binary .add 26 16 20,.load 27 26,
  .ifLt 21 27 (.ifEq 22 0 .nop appendQuad) .nop,.binary .add 15 15 1]

/-- Publish the actual length after all three ordered passes. -/
def finish : Code := .block [.constant 25 29,.binary .add 25 12 25,.store 25 14]

/-- The fixed sparse external argument source program. -/
def program : Code := setup.seq ((FragmentBucket.forEach 15 7 (cableStep false)).seq
  ((FragmentBucket.forEach 15 7 (cableStep true)).seq ((FragmentBucket.forEach 15 9 dataStep).seq finish)))

/-- Exact list specified by the three public scan passes. -/
def Layout.stream (l : Layout) (m : ℕ → ℕ) :=
  Diagonal.ExternalSew.Fragments.stream l.host m (fun c => m (l.supplied+c))
    ((List.range l.count).map (l.row m))

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
