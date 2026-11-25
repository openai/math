import OAI.ThreeFlat.Diagonal.PhysicalNodeBankLayout
import OAI.ThreeFlat.Diagonal.NavigationArchiveFields
import OAI.ThreeFlat.RAM.NavigationNodeRowProgram

namespace OAI
/-! # The compact stage-header tape used by the native node row loop -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM.NavigationNodeRows
open scoped Fin.CommRing Classical

def nodeTape (banks : Banks) (first : ℕ) : List Layers → List ℕ
  | [] => []
  | row :: rest => List.ofFn (fun i : Fin 16 => header banks row.actual row.parent (first+16) i.val) ++
    nodeTape banks (first+16) rest

@[simp] theorem nodeTape_length (banks : Banks) (first : ℕ) (s : List Layers) :
    (nodeTape banks first s).length=16*s.length := by
  induction s generalizing first with
  | nil => rfl
  | cons hd tail ih =>
    simp only [nodeTape,List.length_append,List.length_ofFn,ih,List.length_cons,Nat.mul_succ]; omega

namespace NodePublication
open Computability.VPVNP.BurstRAM
variable {W : ℕ}

def tapeWord (a : NodeArchive) (rows : List Layers) (x : ℕ) : Word W :=
  ((nodeTape a.banks a.headerBase rows)[x-a.headerBase]?.getD 0 : ℕ)

end NodePublication
end ThreeFlat.Diagonal.NavigationPass

end OAI
