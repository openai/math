import OAI.Hierarchy.DescentExteriorReelPrograms

import OAI.Hierarchy.DescentNativeExteriorMatrix
import OAI.Hierarchy.DescentExteriorNativeMatrix

namespace OAI
/-! # One common selected matrix register installs the literal service for all slabs -/
namespace Hierarchy.DescentExteriorShelf
open DescentGL DescentExterior DescentExteriorMatrixUpdate Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w j r t e : ℕ}
local notation "H" => span j r t e
local notation "k" => j+(j+r)

theorem issued_loaded (origin atWord:ℕ) (m:Memory w) (M P:Fin e→Layout k)
    (x:Fin e→Plane j r→Fin t→Bool) (z:Hidden e j r t→Bool)
    (prior:Loaded origin P x z m) (read:∀s:Fin e,m atWord=((matrixCode (M s)).val:Word w)) :
    Loaded origin M x z (issued (j:=j) (r:=r) (t:=t) (e:=e) origin atWord m) := by
  apply install_image origin P M x z (broadcast atWord) m _ prior rfl
  intro i
  have lo:origin+H≤origin+H+i.val:=by omega
  have hi:origin+H+i.val<origin+H+e:=by have:=i.isLt;omega
  simpa [issued,ProtocolRAM.image,fillSegment,lo,hi,broadcast,Expr.eval,Bank.read,Bank.size] using read i

theorem outside_updates (cells:ℕ→Cell) (m:Memory w) (age:ℕ) (address:ℕ)
    (earlier:∀t<age,(cells t).updated<address) : reached cells m age address=m address := by
  induction age with
  | zero=>rfl
  | succ i ih=>
    have h:¬address<(cells i).updated+1:=by have:=earlier i (Nat.lt_succ_self _);omega
    simp only [reached,Cell.after,ProtocolRAM.image,fillSegment,h,and_false,ite_false]
    exact ih (fun t ht=>earlier t (by omega))

theorem frames (origin:ℕ) (P:Fin e→Layout k) (x:Fin e→Plane j r→Fin t→Bool)
    (z:Hidden e j r t→Bool) (cells:ℕ→Cell) (m:Memory w) (age:ℕ)
    (printed:Loaded origin P x z m) (early:∀t<age,(cells t).updated<origin) :
    Loaded origin P x z (reached cells m age) := by
  intro col u live
  rw [outside_updates]
  · exact printed col u live
  · intro i hi
    have h:=early i hi
    change (cells i).updated<origin+col.val*H+u
    omega

end
end Hierarchy.DescentExteriorShelf

end OAI
