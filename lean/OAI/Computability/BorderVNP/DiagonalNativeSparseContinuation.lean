import OAI.Computability.BorderVNP.DiagonalNativeTypedRows
import OAI.Computability.BorderVNP.CellSparseExteriorDriver

/-! # The positive native continuation with physical sparse exterior packets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM CellSparse CellDispatch

/-- Build the true typed source used by the positive branch from stored seven-word
tasks and the private sparse-exterior routine. Each physical burst contains the
supplied intervals and reports. The semantic cell reads the restored zero-filled
logical coordinates throughout its original signed instruction stream. -/
noncomputable def TypedRowsAt.ofSparseRows {w n table count : ℕ} (pub : Arg → Word w) (m : Memory w)
    (tasks : ℕ → TypedBatch.Task) (D : ℕ → Directory) (privateWires : ℕ → ℕ) (external : ℕ → SparseExterior.Field)
    (frame : (pub 0).val+90 < 2^w) (width : (m ((pub 0).val+30)).val=w)
    (base : (m ((pub 0).val+89)).val=table) (len : (m ((pub 0).val+90)).val=count) (space : table+7*count ≤ 2^w)
    (allocated : TypedBatch.Allocated w table count tasks)
    (stored : ∀ i < count, (tasks i).Stored m table i ∧ (tasks i).cell.Stored m)
    (taskRoom : ∀ i < count, (tasks i).callRow+2 < 2^w ∧ (tasks i).cell.Room w)
    (control : TypedBatch.ControlLayout pub m tasks count)
    (directory : let f := Frame.ofMemory pub m
      f.base+3*f.count ≤ 2^w)
    (placed : TypedBatch.PlacedRows pub m tasks count n (fun i => ⟨D i,privateWires i,(external i).bytes⟩))
    (valid : ∀ i < (Frame.ofMemory pub m).count, (m ((Frame.ofMemory pub m).address i)).val=(Frame.ofMemory pub m).team →
      (D i).ProfileWidths ∧ SparseExterior.clock w (D i) (privateWires i) (external i) ≤ n^25) :
    TypedRowsAt SparseExterior.driver n pub m where
  table := table
  count := count
  tasks := tasks
  cells i := ⟨D i,privateWires i,(external i).values⟩
  payload i := Packet.input (D i) (privateWires i) (external i).bytes
  frame := frame
  width := width
  base := base
  len := len
  space := space
  allocated := allocated
  stored := stored
  taskRoom := taskRoom
  control := control
  directory := directory
  packed := SparseExterior.packedRows D privateWires external (by
    by_contra! z
    have wz : w=0 := by omega
    have top : 90 < 2^w := by omega
    rw [wz,pow_zero] at top
    omega) placed allocated (fun i hi => (taskRoom i hi).2) control valid

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
