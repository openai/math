import OAI.Hierarchy.ProbeActualGroups
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenCount

namespace OAI
/-! # Ordinals of the physical stage and signed direction -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen
open ProbeStage
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

abbrev Key (z d k : ℕ) := Fin ((permutationFabric z d).shapes.length*(2*k))
def key (t : StageAt z d) (j : Fin (2*k)) : Key z d k := finProdFinEquiv (t,j)
def stage (i : Key z d k) : StageAt z d := (finProdFinEquiv.symm i).1
def axis (i : Key z d k) : Fin (2*k) := (finProdFinEquiv.symm i).2
@[simp] theorem stage_key (t : StageAt z d) (j : Fin (2*k)) : stage (key t j)=t := by simp [stage,key]
@[simp] theorem axis_key (t : StageAt z d) (j : Fin (2*k)) : axis (key t j)=j := by simp [axis,key]
@[simp] theorem key_pair (i : Key z d k) : key (stage i) (axis i)=i :=
  finProdFinEquiv.apply_symm_apply i

end
end Hierarchy.ProtocolRAM.PurchaseFrozen

end OAI
