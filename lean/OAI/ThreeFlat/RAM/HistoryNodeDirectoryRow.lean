import OAI.ThreeFlat.RAM.HistoryNodeDirectoryFields
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveRun

namespace OAI
/-! # The five directory fields of every genuinely published chronological node -/

namespace ThreeFlat.RAM.HistoryStageSetup
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.NavigationPass Diagonal.NavigationPass.NodePublication NavigationNodeRows
open scoped Fin.CommRing
variable {W : ℕ}

theorem published_directory {rs : List Layers} (a : NodeArchive) (P : Program rs) (initial : Memory W)
    {budget : ℕ} (room : RunBounds W a rs budget) (ordered : Chronological rs) (i : Fin rs.length)
    (j : Fin (rs.get i).actual.count) :
    DirectoryRow a.banks (rs.get i).actual j (state a P initial rs.length) := by
  have row := final_node_word a P initial room ordered i j
  refine ⟨row 3,row 4,row 5,row 6,?_⟩
  have charge := final_charge_word a P initial room ordered i j (1 : Fin 2)
  change state a P initial rs.length
    (a.banks.charges+2*((rs.get i).actual.first+j.val)+1) = _ at charge
  rw [charge]
  have ext := row (7 : Fin 8)
  change state a P initial rs.length (a.banks.nodes+8*((rs.get i).actual.first+j.val)+7) =
    ((2*(P.data i).cost a.banks (prior a (decrement a (state a P initial i.val))) j 1 : ℕ) : Word W) at ext
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using ext

end ThreeFlat.RAM.HistoryStageSetup

end OAI
