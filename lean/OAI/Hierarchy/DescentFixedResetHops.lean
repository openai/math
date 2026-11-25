import OAI.Hierarchy.DescentExteriorStaticHops
import OAI.Hierarchy.DescentFixedResetGeometry

namespace OAI
/-! # The issued reset uses the original public pitch and every original trunk lookup -/
namespace Hierarchy.DescentExteriorReplay.HopTables
open DescentCompiler DescentSixParty DescentCommonHost DescentDenseHostOrder
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
    {W : MarkedWorld F d P bits} {input : Reached W G q ε S k i z D w hist}
    {ctl : ResetRates G S k D n h C f g cut tail}

theorem reset_hop_geometry {D₀ n₀ h₀ C₀ f₀ g₀ cut₀ tail₀ : ℕ} (b : ClosedReset input ctl)
    (initial : ResetRates G S k D₀ n₀ h₀ C₀ f₀ g₀ cut₀ tail₀)
    (same : Chronology.resetSpec b=RotorSpec.ofRates initial) :
    (roster b.reset.graph (b.reset.k-b.terminals.commonDepth) (GroupStage.depthBound D n f g)).card=
      resetPitch initial.board k (GroupStage.depthBound D₀ n₀ f₀ g₀) ∧
    b.localTrunk=resetShape initial.board k (GroupStage.depthBound D₀ n₀ f₀ g₀) k g₀ := by
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,_,boards⟩:=ctl.same_geometry initial same
  have actual:=reset_public b
  rw [eq_of_heq boards] at actual
  exact actual

end
end Hierarchy.DescentExteriorReplay.HopTables

end OAI
