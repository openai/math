import OAI.Computability.BorderVNP.CellSparseExteriorNative
import OAI.Computability.BorderVNP.CellSparseExteriorDriver
import OAI.Computability.BorderVNP.RoutingISATypedBatchEntry

/-! # Replacing the live external pointer in the seven-word typed call rows

The original logical cell bank and its report tail stay at their physical
addresses. The scanner reads the compact cell and span directories, encodes
only the true live data at the reserved compressed address, and publishes the
two fields consumed by the subsequent typed initializer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacketEncode

/-- Absolute pointers of the real compact task table and the sparse argument arenas. -/
structure Layout where
  /-- Base address of the team frame. -/
  frame : ℕ
  /-- Address of the extended geometry control header. -/
  control : ℕ
  /-- Number of compact rows owned by the team. -/
  count : ℕ
  /-- Address of the seven-word task array. -/
  tasks : ℕ
  /-- Address of the six-word owned-cell metadata. -/
  six : ℕ
  /-- Start of the per-cell fragment offset and count pairs. -/
  pairs : ℕ
  /-- Start of the stable fragment descriptor triples. -/
  triples : ℕ
  /-- Start of the reserved compressed external buffers. -/
  compact : ℕ
  /-- Reserved external-buffer words per global cell. -/
  stride : ℕ
  /-- Address of the used external lengths indexed by global cell. -/
  counts : ℕ

/-- The global host ordinal, dense bank and owned section of one typed row. -/
structure Owned where
  /-- Global cell ordinal in the full call directory. -/
  global : ℕ
  /-- Address of its logical supplied bank in team memory. -/
  dense : ℕ
  /-- Index of its first live fragment in the bucket. -/
  first : ℕ
  /-- Live fragment and report data for this cell. -/
  field : Field

/-- The original typed row and six-word header name the same supplied region. -/
structure Owned.Stored (o : Owned) (l : Layout) (i : ℕ) (m : ℕ → ℕ) : Prop where
  number : m (l.six+6*i)=o.global
  width : m (l.six+6*i+2)=o.field.width
  base : m (l.tasks+7*i+2)=o.dense
  size : m (l.tasks+7*i+3)=o.field.width+o.field.tail.length
  start : m (l.pairs+2*o.global)=o.first
  length : m (l.pairs+2*o.global+1)=o.field.spans.length

/-- The finite set of scalar addresses used by the batch row loader. -/
def Owned.addresses (o : Owned) (l : Layout) (i : ℕ) :=
  [l.six+6*i,l.six+6*i+2,l.tasks+7*i+2,l.tasks+7*i+3,l.pairs+2*o.global,l.pairs+2*o.global+1]

/-- Actual compressed field address in this team's workspace. -/
def Owned.dest (o : Owned) (l : Layout) := l.compact+o.global*l.stride

/-- Logical source intervals and staging destinations all lie in machine address space. -/
structure Owned.Fits (o : Owned) (l : Layout) (i w : ℕ) : Prop where
  constants : 7 < 2^w
  header : l.six+6*i+2 < 2^w
  task : l.tasks+7*i+3 < 2^w
  pair : l.pairs+2*o.global+1 < 2^w
  triples : l.triples+3*(o.first+o.field.spans.length) < 2^w
  tail : o.dense+o.field.width+o.field.tail.length < 2^w
  output : o.dest l+o.field.bytes.length < 2^w
  counter : l.counts+o.global < 2^w
  advance : i+1 < 2^w

/-- Numeric memory image of one native compression and publication. -/
def Owned.image (o : Owned) (l : Layout) (i : ℕ) (m : ℕ → ℕ) :=
  let z := putDigits m (o.dest l) o.field.bytes
  let z := Function.update z (l.tasks+7*i+2) (o.dest l)
  let z := Function.update z (l.tasks+7*i+3) o.field.bytes.length
  Function.update z (l.counts+o.global) o.field.bytes.length

/-- Read an indirect sparse arena control word; register 61 retains the actual header. -/
private def controlWord (r : Reg) (offset : Word 8) :=
  Code.block [.constant 63 offset,.binary .add 62 61 63,.load r 62]

/-- Load the ordinary owned-task and six-word bases, bucket starts and reserved
compressed output. The task loop only iterates over physically owned cells. -/
def setup : Code := .block [
  readFrame 40 62 63 90,readFrame 41 62 63 89,readFrame 61 62 63 92,
  controlWord 42 17,controlWord 43 31,controlWord 44 32,controlWord 45 34,
  controlWord 46 35,controlWord 47 36,.constant 48 0,.constant 53 1]

/-- Set the single-cell writer's six input registers from the actual table words. -/
def readOwned : Code := .block [
  .constant 54 6,.binary .mul 54 48 54,.binary .add 54 42 54,.load 50 54,
  .constant 55 2,.binary .add 54 54 55,.load 23 54,
  .constant 54 7,.binary .mul 54 48 54,.binary .add 49 41 54,
  .binary .add 49 49 55,.load 24 49,.binary .add 54 49 53,.load 25 54,
  .binary .add 24 24 23,.binary .sub 25 25 23,
  .binary .mul 54 50 55,.binary .add 54 43 54,.load 56 54,.binary .add 54 54 53,.load 57 54,
  .constant 55 3,.binary .mul 21 56 55,.binary .add 21 44 21,.binary .mul 22 57 55,.binary .add 22 21 22,
  .binary .mul 51 50 46,.binary .add 51 45 51,.copy 20 51,.binary .add 52 47 50]

/-- Publish the encoded external base and length in the original typed row,
plus the actual used length at the sparse-arena count word. -/
def publish : Code := .block [.binary .sub 54 20 51,.store 49 51,.binary .add 49 49 53,
  .store 49 54,.store 52 54,.binary .add 48 48 53]

/-- Compress one genuine cell and advance the compact task row. -/
def step : Code := .seq readOwned (.seq Native.write publish)

/-- The fixed native sparse exterior stage. Invoke it after the supplemental
descriptor prepass and immediately before the true typed initializer. -/
def prepare : Code := .seq setup (.whileLt 48 40 step)

/-- No private choices or premature halts occur in the sparse serialization stage. -/
theorem ordinary : prepare.deterministic=true ∧ prepare.withoutAccept=true := by decide

/-- Registers held across the scan and each invocation of the private-burst writer. -/
def Layout.Ready (l : Layout) (i : ℕ) (s : Reg → ℕ) : Prop :=
  s 40=l.count ∧ s 41=l.tasks ∧ s 42=l.six ∧ s 43=l.pairs ∧ s 44=l.triples ∧ s 45=l.compact ∧
  s 46=l.stride ∧ s 47=l.counts ∧ s 48=i ∧ s 53=1

/-- Live native operands on entry to the RLE writer, including registers retained
for subsequent publication into the current typed row. -/
def Owned.Ready (o : Owned) (l : Layout) (i : ℕ) (s : Reg → ℕ) : Prop :=
  l.Ready i s ∧ s 21=l.triples+3*o.first ∧ s 22=l.triples+3*(o.first+o.field.spans.length) ∧
  s 23=o.field.width ∧ s 24=o.dense+o.field.width ∧ s 25=o.field.tail.length ∧ s 20=o.dest l ∧
  s 49=l.tasks+7*i+2 ∧ s 51=o.dest l ∧ s 52=l.counts+o.global

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
