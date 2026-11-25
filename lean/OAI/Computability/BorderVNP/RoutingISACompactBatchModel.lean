import OAI.Computability.BorderVNP.RoutingISAExternalSeedModel
import OAI.Computability.BorderVNP.RoutingISACompactWrite

/-! # Batch preparation of signed private cell arguments

Each five-word task descriptor names the live boundary inputs, the scratch region with its
private program suffix, and the output word interval. The fixed loop reads those fields,
materializes the boundary literal records, then packs the complete descriptor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CompactBatch

open VPVNP.BurstRAM Packing.Directory.ISA

/-- One cell's live external wires, serialized suffix, and placement addresses. -/
structure Task where
  /-- Address of the first live external wire. -/
  extBase : ℕ
  /-- Base of the one-bit-per-word temporary payload. -/
  scratch : ℕ
  /-- Address of the compact word burst. -/
  dest : ℕ
  /-- Boundary wire bits in their stack order. -/
  external : List Bool
  /-- The generator's previously placed serialized body. -/
  suffix : List Bool

/-- Complete compact-generator payload. -/
def Task.payload (t : Task) := CompactMachine.externalRecords t.external ++ t.suffix

/-- Result of the native boundary prefix stores. -/
def Task.seed {w : ℕ} (t : Task) (m : Memory w) : Memory w :=
  putWords m t.scratch ((CompactMachine.externalRecords t.external).map (fun b => DiagonalResidueRAM.word w b.toNat))

/-- Result of the two actual consecutive output stages for this cell. -/
def Task.write {w : ℕ} (t : Task) (m : Memory w) : Memory w :=
  putWords (t.seed m) t.dest (CompactFrame.pack w t.payload)

/-- Physical memory after the prefix of the cell task table. -/
def written {w : ℕ} (original : Memory w) (tasks : ℕ → Task) : ℕ → Memory w
  | 0 => original
  | i+1 => (tasks i).write (written original tasks i)

/-- Live public pointer and length fields of one fixed-format task. -/
def Task.Stored {w : ℕ} (t : Task) (m : Memory w) (table i : ℕ) : Prop :=
  (m (table+5*i)).val = t.extBase ∧ (m (table+5*i+1)).val = t.external.length ∧
    (m (table+5*i+2)).val = t.scratch ∧ (m (table+5*i+3)).val = t.payload.length ∧
    (m (table+5*i+4)).val = t.dest

/-- Both the actual external bits and the serialized body suffix are present at row entry. -/
def Task.Input {w : ℕ} (t : Task) (m : Memory w) : Prop :=
  CompactWrite.Source m t.extBase t.external ∧
    CompactWrite.Source m (t.scratch + 12*t.external.length) t.suffix

/-- Numeric and separation bounds for the two single-cell native writers. -/
structure Task.Fits (t : Task) (w : ℕ) : Prop where
  /-- All external wire addresses fit. -/
  ext : t.extBase + t.external.length ≤ 2^w
  /-- The prefix writer's final address increment fits. -/
  prefixFit : t.scratch + 12*t.external.length < 2^w
  /-- The complete source payload fits in the address space. -/
  scratch : t.scratch + t.payload.length ≤ 2^w
  /-- The compact output words fit. -/
  dest : t.dest + (CompactFrame.pack w t.payload).length ≤ 2^w
  /-- Source wires survive all prefix writes. -/
  extSeparate : CompactWrite.Disjoint t.extBase t.external.length t.scratch (12*t.external.length)
  /-- The serializer's input survives its packed output stores. -/
  packSeparate : CompactWrite.Disjoint t.scratch t.payload.length t.dest (CompactFrame.pack w t.payload).length

/-- Initialize the scan cursor and the constant row stride. -/
def setup : Code := .block [.constant 39 1, .constant 34 0, .constant 35 5]

/-- Fetch the five words of the live task descriptor. -/
def fetch : Code := .block [.binary .mul 36 35 34, .binary .add 36 32 36, .load 3 36,
  .binary .add 36 36 39, .load 4 36, .binary .add 36 36 39, .load 5 36,
  .binary .add 36 36 39, .load 37 36, .binary .add 36 36 39, .load 38 36]

/-- After seed writes, prepare the source, full length and destination of the packer. -/
def move : Code := .block [.copy 3 5, .copy 4 37, .copy 5 38]

/-- One native row, from fetch to completed packed burst. -/
def body : Code := .block [fetch, ExternalSeed.writer, move, CompactWrite.writer, .binary .add 34 34 39]

/-- The fixed batch table, returning after the last descriptor. -/
def scan : Code := .seq setup (.whileLt 34 33 body)

/-- Per-row instruction allowance excluding its loop guard. -/
def Task.cost (t : Task) := fetch.slots + ExternalSeed.setup.slots +
  (ExternalSeed.step.slots+1)*t.external.length+2 + move.slots + CompactWrite.setup.slots +
  (CompactWrite.step.slots+1)*t.payload.length+2 + 1

/-- Width, table base, row count, cursor and stride maintained across the two writers. -/
def Ready {w : ℕ} (table count i : ℕ) (s : Bank w) : Prop :=
  (s 39).val = 1 ∧ (s 2).val = w ∧ (s 32).val = table ∧ (s 33).val = count ∧
  (s 34).val = i ∧ (s 35).val = 5

end RoutingISA.CompactBatch

end BorderVNP
end Computability
end OAI
