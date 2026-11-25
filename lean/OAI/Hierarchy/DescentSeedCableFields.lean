import OAI.Hierarchy.DescentSeedCableMeaning
import OAI.Hierarchy.DescentPackedSeedLegs
import OAI.Hierarchy.DescentSeedPanelReceipt
import OAI.Hierarchy.DescentTerminalPortChart

namespace OAI
/-! Original edge names in the first occupied grain of a seed cable. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentColonies DescentSixParty DescentSharedCableNames DescentKernelHistory
open Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F V : Type} [Field F] [Fintype V] [DecidableEq V] {cp pins r s : ℕ}
    (X : Approximation F cp pins) {G : PoweredGadget F} {q ε : ℝ} (S : DescentCompiler.AtomSchedule)
    {c : (initialGroup X S.copies s).Choice}
    (A : GroupStage ((initialGroup X S.copies s).state c) G q ε (Fin (S.groupCount 0)) V r)
    (order : ((initialGroup X S.copies s).state c).graph.Edge↪ℕ) (vertex : V↪Fin (Fintype.card V))

@[simp] theorem liftLeg_cable {R : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X)
    (e : {f : Cable X // DescentInitialHost.source X.network.copyGraph f=v ∨ DescentInitialHost.target X.network.copyGraph f=v}) :
    liftLeg X c j v (.inl e)=.inl (liftCable X c j v e) :=rfl

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
