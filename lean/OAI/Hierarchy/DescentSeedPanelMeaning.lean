import OAI.Hierarchy.DescentSeedSignedStencil
import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! A first-stage site ticket links the actually chosen original graph to
every signed word at that ticket, including unoccupied slots and both signs. -/
namespace Hierarchy.DescentPackedSeed.Signed.Plane
open DescentSeedRoot DescentInitialHost DescentColonies DescentSixParty DescentSharedCableNames
open Catalyst
open scoped Classical Fin.CommRing
noncomputable section
variable {F V : Type} [Field F] [Fintype V] [DecidableEq V] {cp pins r s : ℕ}
  (X:Approximation F cp pins) {G:PoweredGadget F} {q ε:ℝ} (S:DescentCompiler.AtomSchedule)
  {c:(initialGroup X S.copies s).Choice}
  (A:GroupStage ((initialGroup X S.copies s).state c) G q ε (Fin (S.groupCount 0)) V r)
  (order:((initialGroup X S.copies s).state c).graph.Edge↪ℕ) (vertex:V↪Fin (Fintype.card V))
  (size:Fintype.card V=Fintype.card (Vertex X))
def initialTicket (v:V):Vertex X:=(Fintype.equivFin (Vertex X)).symm (Fin.cast size (vertex v))
def panelNames:Stage.Host (Fin (S.groupCount 0)) V r↪ℕ:=
  DescentPacking.PackedMatch.Local.Stage.cableNames r (DescentStageEdgeReceipt.groupRank Fin.valEmbedding (vertex.trans Fin.valEmbedding))
def Receipt:Prop:=
  ∀ (valid:A.StateBounds S 0) (g:Fin (S.groupCount 0)) (v:V) (x:Block r) (j:Fin (2*A.cap)),
    (DescentSignedCableCodec.encode (Stage.signedPanel A order S valid (panelNames (r:=r) S vertex) ((g,v),x) j)).val=
    let part:Fin 2×Fin 256:=finProdFinEquiv.symm (j.val:Fin (2*256))
    (DescentSignedCableCodec.encode (panel X (initialTicket X vertex size v) (finTwoEquiv part.1) part.2.val)).val
end
end Hierarchy.DescentPackedSeed.Signed.Plane

end OAI
