import OAI.Hierarchy.DescentSeedPanelMeaning
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

def liftCable {R : ℕ} (c : (initialGroup X R s).Choice) (j : Fin R) (v : Vertex X)
    (e : {f : Cable X // DescentInitialHost.source X.network.copyGraph f=v ∨ DescentInitialHost.target X.network.copyGraph f=v}) :
    Incident ((initialGroup X R s).state c).graph ⟨j,v⟩ :=
  ⟨⟨j,e.val⟩,e.property.imp (congrArg (Sigma.mk j)) (congrArg (Sigma.mk j))⟩

def CableFields : Prop :=
  ∀(valid : A.StateBounds S 0) (j : Fin S.copies) (v : Vertex X)
    (e : {f : Cable X // DescentInitialHost.source X.network.copyGraph f=v ∨ DescentInitialHost.target X.network.copyGraph f=v})
    (alive : 0<A.grainCount (liftCable X c j v e).val),
    let h:=Stage.home A ⟨j,v⟩
    let p:=DescentTerminalPortChart.first A ⟨j,v⟩ (liftCable X c j v e) alive
    let wing:=Stage.live A order S valid (panelNames (r:=r) S vertex) h p
    wing.neighbor.val=seedPeer X v e.val ∧ wing.wire.val=seedParallel X v e.val

end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
