import OAI.Computability.BorderVNP.CellPacketInitializer
import OAI.Computability.BorderVNP.RoutingISACompactFrame
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-!
# A public task directory for preparing privately typed cell arguments

Each row names the chunk range, the live boundary range, the temporary bit region,
the compact output and the owner word of the final three-word call row. The caller
stores the *returned* pointer and word count into the two argument columns.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM Packing.Directory.ISA
open RationalHitting.StackLanguage

/-- Addresses and decoded contents of one task of the current team. -/
structure Task where
  /-- The actual public/private chunk initializer and its live memory interpretation. -/
  cell : CellPacket.Task
  /-- Address of the owner column in the outer call directory. -/
  callRow : ℕ

/-- Publish the returned start and word count to the directory read by the dispatch loop. -/
def Task.publish {w : ℕ} (t : Task) (m : Memory w) : Memory w :=
  Function.update (Function.update m (t.callRow+1) (DiagonalResidueRAM.word w t.cell.burstBase))
    (t.callRow+2) (DiagonalResidueRAM.word w (t.cell.burst w).length)

/-- Cumulative stores after the first tasks of this team. -/
def written {w : ℕ} (original : Memory w) (tasks : ℕ → Task) : ℕ → Memory w
  | 0 => original
  | j+1 => (tasks j).publish ((tasks j).cell.image (written original tasks j))

/-- Exact contents of the seven words consumed by a row of the task scan. -/
def Task.Stored {w : ℕ} (t : Task) (m : Memory w) (base i : ℕ) : Prop :=
  let a := base+7*i
  (m a).val=t.cell.descriptorBase ∧ (m (a+1)).val=(t.cell.descriptorBase+3*t.cell.chunks.length) ∧ (m (a+2)).val=t.cell.externalBase ∧
    (m (a+3)).val=t.cell.external.length ∧ (m (a+4)).val=t.cell.scratchBase ∧ (m (a+5)).val=t.cell.burstBase ∧
    (m (a+6)).val=t.callRow

/-- Set the independent outer cursor and constants for scanning seven-word tasks. -/
def setup : Code := .block [.constant 43 0, .constant 44 7, .constant 47 1]

/-- Fetch the seven actual parameters, then install the one-cell initializer's constants. -/
def fetch : Code := .block [
  .binary .mul 45 43 44, .binary .add 45 41 45, .load 2 45,
  .binary .add 45 45 47, .load 3 45,
  .binary .add 45 45 47, .load 4 45,
  .binary .add 45 45 47, .load 5 45,
  .binary .add 45 45 47, .load 6 45,
  .binary .add 45 45 47, .load 7 45,
  .binary .add 45 45 47, .load 46 45,
  .constant 0 0, .constant 1 1, .constant 18 2, .copy 8 40, .copy 20 6]

/-- Store the actual initializer outputs and advance the task cursor. -/
def publish : Code := .block [.binary .add 45 46 47, .store 45 5, .binary .add 45 45 47,
  .store 45 15, .binary .add 43 43 47]

/-- One physical task; the initializer is a fixed subprogram independent of the row. -/
def body : Code := .seq fetch (.seq CellPacket.initializer publish)

/-- The complete fixed scan of the current team's preparation tasks. -/
def scan : Code := .seq setup (.whileLt 43 42 body)

/-- High registers that survive each cell initializer and remain live between tasks. -/
def Ready {w : ℕ} (base count i : ℕ) (s : Bank w) : Prop :=
  (s 40).val=w ∧ (s 41).val=base ∧ (s 42).val=count ∧ (s 43).val=i ∧
    (s 44).val=7 ∧ (s 47).val=1

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
