import OAI.Hierarchy.DescentArchiveRankData
import OAI.Hierarchy.DescentHiddenOrder
import OAI.Hierarchy.DescentScheduledBitHistory
import OAI.Hierarchy.DescentStageEdgeReceipt

namespace OAI
/-! # Stable private-word and public-cable addresses under the full ordinary normalization -/

namespace Hierarchy.DescentHistoryOrder
open DescentKernelHistory DescentSixParty DescentStageEdgeReceipt DescentCableUnbundling DescentHostDirectory
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pins : P→ℕ} {W : MarkedWorld F d P pins}
abbrev WireRank (W : MarkedWorld F d P pins) := W.graph.Edge↪ℕ

/-- Each merge adds physical surviving-parent cable addresses, and a split changes
only the public cable offset. No arbitrary enumeration of the accumulated hidden names occurs. -/
def followed (n : Normalize W) : (B : BitDescription W) → SiteRank B → WireRank W →
    SiteRank (BitDescription.follow n B) := by
  induction n with
  | done W=>intro B old _; exact old
  | merge W A key flag k g rest ih=>
    intro B old edge
    exact ih _ (coalescedHidden B old key flag k g edge) ((Function.Embedding.subtype _).trans edge)
  | split W q m fit rest ih=>
    intro B old edge
    exact ih _ (piecesHidden B old q m fit) ((chronological W.graph W.core m q edge edge.injective).toEmbedding.trans Fin.valEmbedding)
  | named W site edge rest ih=>
    intro B old rank
    exact ih _ ((renamedHidden B site edge).toEmbedding.trans old) (edge.symm.toEmbedding.trans rank)

private def castSiteRank {X Y : MarkedWorld F d P pins} (h : X=Y) (b : BitDescription X)
    (e : SiteRank b) : SiteRank (cast (congrArg BitDescription h) b) := by subst Y; exact e

private def castWireRank {X Y : MarkedWorld F d P pins} (h : X=Y) (e : WireRank X) : WireRank Y := by subst Y; exact e

variable {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε)
variable (B : BitDescription W) (c : (T.result he).Choice)

def scanRanks (old : SiteRank B) (e : W.graph.Edge≃Fin (Fintype.card W.graph.Edge))
    (pair : (BitDescription.scannedRows he T).pairs≃Fin (Fintype.card (BitDescription.scannedRows he T).pairs)) :
    SiteRank (BitDescription.scanned he T B c) × WireRank ((T.result he).state c) :=
  let r := BitDescription.scannedRows he T
  let b := B.selected G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit (fun _=>le_refl T.z)
    r.pack (r.profile c)
  let h : SiteRank b := selectedHidden B old G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit (fun _=>le_refl T.z)
    r.pack (r.profile c) e pair
  let cables : WireRank (W.selected G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit r.pack (r.profile c)) :=
    (Function.Embedding.subtype _).trans ⟨MarkedWorld.edgeNumber W e pair,MarkedWorld.edgeNumber_inj W e pair⟩
  ⟨castSiteRank (r.state c).symm b h,castWireRank (r.state c).symm cables⟩

def ordinaryRank (n : Normalize ((T.result he).state c)) (old : SiteRank B)
    (e : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : (BitDescription.scannedRows he T).pairs≃Fin (Fintype.card (BitDescription.scannedRows he T).pairs)) :
    SiteRank (BitDescription.follow n (BitDescription.scanned he T B c)) :=
  let k:=scanRanks he T B c old (dense e) pair
  followed n _ k.1 k.2

end
end Hierarchy.DescentHistoryOrder

end OAI
