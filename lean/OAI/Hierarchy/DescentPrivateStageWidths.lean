import OAI.Hierarchy.DescentRecordedBranch
import OAI.Hierarchy.DescentPickedAtomCount

namespace OAI
/-! # The complete wire volume before a selected motif is contracted -/
namespace Hierarchy.DescentHistoryOrder
open Computability.BorderVNP.Crossing DescentSixParty GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {F P I : Type} [Field F] [Fintype I] {D : ℕ} {bits : P→ℕ}
variable (G : PoweredGadget F) (W : MarkedWorld F D P bits) (pick : I×Fin 2 ↪ W.graph.Edge)
variable (z : I→ℕ) (p : I→Profile G.C)
local notation "N" => physical W.graph pick (branchWidth G z p)

omit [Fintype I] in
/-- Each two paid demands have width `2*z*b`. Even before contraction, their
eight new cables together require at most `4*z*b` bit positions. -/
theorem supply_at_most_twice (i : I) :
    (∑e,branchWidth G z p i e)≤2*(2*(z i*G.b)) := by
  unfold branchWidth
  rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have budget : ((∑e,((p i).1 e).val)+8*G.k)≤4*G.b :=
    (Nat.add_le_add_right (p i).property _).trans G.paid.le
  calc
    _=z i*((∑e,((p i).1 e).val)+8*G.k) := by simp
    _≤z i*(4*G.b) := Nat.mul_le_mul_left _ budget
    _=_ := by ring

theorem physical_width_le (onCore : ∀t,pick t∈W.core) (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) :
    (∑e,(N).width e)≤W.tetherWidth+4*W.liveWidth := by
  have twice : (∑t : I×Fin 2,W.graph.width (pick t))=∑i,2*(z i*G.b) := by
    rw [Fintype.sum_prod_type]
    simp [fit,Nat.mul_comm]
  have addOn : (∑t : I×Fin 8,branchWidth G z p t.1 t.2)≤2*(∑t : I×Fin 2,W.graph.width (pick t)) := by
    rw [twice,Finset.mul_sum,Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun i _=>supply_at_most_twice G z p i
  have selected:=W.picked_width_sum pick onCore
  have volume : W.liveWidth+W.tetherWidth=∑e,W.graph.width e := Finset.sum_add_sum_compl W.core _
  change (∑e : W.graph.Edge⊕((I×Fin 2)⊕(I×Fin 8)),GadgetNetwork.width W.graph pick (branchWidth G z p) e)≤_
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  change (∑e,W.graph.width e)+((∑t : I×Fin 2,W.graph.width (pick t))+(∑t : I×Fin 8,branchWidth G z p t.1 t.2))≤_
  omega

end
end Hierarchy.DescentHistoryOrder

end OAI
