import OAI.Hierarchy.DescentRetainedAssignedDigits
import OAI.Hierarchy.DescentRetainedCompactBounds

namespace OAI
/-! # The physical retained reset kind at every output socket -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentResetRetainedSetup DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentResetOperandSetup.Chart)
variable (hostEq : C.placement.oldHosts=C.retained.hosts) (groupEq : C.placement.groups*C.placement.blocks=C.retained.grouped)
    (which : C.seven.control.Targets) (packet : C.seven.Packets) (strips : C.retained.Strips)

variable {u : ℕ} (keep : Fin C.placement.shapes→Bool) (name : Fin u→Fin C.placement.sparse)
variable (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (n : Fin C.retained.nodes)
variable (h : Fin C.placement.newHosts) (g : Fin C.placement.groups)
/-- The decoder copies the pin tag and clears every other retained tag before
adding a selected cable. The compact destination may be outside the live roster. -/
theorem assigned_tag_le : (DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch keep name
    (C.assignedDigits hostEq groupEq which packet strips) (C.retained.outputID 1 0 arg n) x h g).val ≤ 2 := by
  apply DescentRetainedTargetPlacement.Chart.compact_le
  intro j u a
  let row:=C.retained.site (C.seven.stripes which packet strips j) (u.cast hostEq) (a.cast groupEq)
  let o := C.retained.outputID 1 0 arg n
  have pairEq := finProdFinEquiv.symm_apply_apply (o,j)
  have first := congrArg (fun (p : Fin C.retained.outputs × Fin C.placement.shapes) =>
    C.seven.decoded which packet strips p.1 p.2 (u.cast hostEq) (a.cast groupEq)) pairEq
  apply le_of_eq_of_le (congrArg Fin.val first)
  let z : Fin ((2*7*C.retained.args)*C.retained.nodes) :=
    finProdFinEquiv (finProdFinEquiv (finProdFinEquiv ((1 : Fin 2),(0 : Fin 7)),arg),n)
  have idx : (finSumFinEquiv.symm o : Fin ((2*7*C.retained.args)*C.retained.nodes) ⊕ Fin C.retained.nodes) =
      .inl z := finSumFinEquiv.symm_apply_apply _
  unfold DescentRetainedSeven.Chart.decoded Layout.function
  erw [idx]
  dsimp only [z]
  erw [finProdFinEquiv.symm_apply_apply,finProdFinEquiv.symm_apply_apply,finProdFinEquiv.symm_apply_apply]
  exact C.retained.decode_kept_tag_le row arg n


end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
