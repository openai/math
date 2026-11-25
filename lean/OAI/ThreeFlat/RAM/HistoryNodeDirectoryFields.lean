import Mathlib.Data.ZMod.Defs
import OAI.Computability.VPVNP.RAMExecution
import OAI.ThreeFlat.RAM.NavigationNodeFields

namespace OAI
/-! # The five words and frame of the original chronological node directory -/

namespace ThreeFlat.RAM.HistoryStageSetup
open Computability.VPVNP.BurstRAM NavigationNodeRows
open scoped Fin.CommRing
variable {W : ℕ}

/-- The physical node descriptor words used by the stage kernel, including the
relation between S44's external pin count and the resident S43 pair count. -/
structure DirectoryRow (b : Banks) (s : Layer) (j : Fin s.count) (mem : Memory W) : Prop where
  childPtr : mem (b.nodes+8*(s.first+j.val)+3)=((s.children+j.val*s.childCount:ℕ):Word W)
  childCount : mem (b.nodes+8*(s.first+j.val)+4)=(s.childCount:Word W)
  kernel : mem (b.nodes+8*(s.first+j.val)+5)=((s.kernels+j.val*5:ℕ):Word W)
  incident : mem (b.nodes+8*(s.first+j.val)+6)=((s.incident+j.val*2:ℕ):Word W)
  external : mem (b.nodes+8*(s.first+j.val)+7)=
    2*mem (b.charges+2*(s.first+j.val)+1)

theorem DirectoryRow.retain {b : Banks} {s : Layer} {j : Fin s.count} {old now : Memory W}
    (row : DirectoryRow b s j old)
    (nodeFrame : ∀ k : Fin 8,3≤k.val→now (b.nodes+8*(s.first+j.val)+k.val)=old (b.nodes+8*(s.first+j.val)+k.val))
    (pairs : now (b.charges+2*(s.first+j.val)+1)=old (b.charges+2*(s.first+j.val)+1)) :
    DirectoryRow b s j now := by
  exact ⟨(nodeFrame 3 (by decide)).trans row.childPtr,(nodeFrame 4 (by decide)).trans row.childCount,
    (nodeFrame 5 (by decide)).trans row.kernel,(nodeFrame 6 (by decide)).trans row.incident,
    (nodeFrame 7 (by decide)).trans (row.external.trans (congrArg (fun a : Word W=>2*a) pairs.symm))⟩

end ThreeFlat.RAM.HistoryStageSetup

end OAI
