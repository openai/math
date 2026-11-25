import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentStateBounds

namespace OAI
/-! # Original paid count at each occupied block -/
namespace Hierarchy.DescentPaidResidentCount
open DescentSixParty
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)
local notation "census" => DescentPacking.PackedMatch.Local.Stage.Census.count A groups hosts

include S ready in
theorem live (b : ℕ) (u : W.graph.Site) :
    census b (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)=((A.records u).length:ℕ) := by
  have member : ∃v,hosts v=hosts (A.pos u).2:=⟨_,rfl⟩
  have slot : member.choose=(A.pos u).2:=hosts.injective member.choose_spec
  simp only [DescentPacking.PackedMatch.Local.Stage.Census.count,dite_eq_left member,slot,Equiv.symm_apply_apply,
    PackedCensus.histories,StarKeys.blockMass,Prod.mk.eta]
  congr 1
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ ne
    have different : ¬(A.pos v=A.pos u ∧ A.block v=A.block u):=fun eqn=>ne (ready.coordinates (Prod.ext eqn.1 eqn.2))
    simp [different]
  · simp

end
end Hierarchy.DescentPaidResidentCount

end OAI
