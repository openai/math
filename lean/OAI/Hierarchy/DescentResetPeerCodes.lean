import OAI.Hierarchy.DescentResetPeerAxes
import OAI.Hierarchy.DescentResetPeerValues

namespace OAI
/-! # Relating raw endpoint words to the actual receiver geometry and local sockets -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetAttachments
open DescentCompiler DescentColonies DescentDenseHostOrder DescentStageEdgeReceipt DescentResetPeerUnionRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "height" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card
local notation "Vnew" => ↥(ResetInput.commonNames B.reset B.terminals)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rank" => (Z).rawHostRank T vertex
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) ((rank).trans Fin.valEmbedding)) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite

theorem peer_words (e : (coarse).graph.Edge) (x y : ℕ) :
    rawPeer B e x y ↔
      (((rank ((blocks B).src e).1.2).val=x ∧ (rank ((blocks B).dst e).1.2).val=y) ∨
       ((rank ((blocks B).dst e).1.2).val=x ∧ (rank ((blocks B).src e).1.2).val=y)) := by
  unfold rawPeer incidentWords
  change 1=1 ∧ _ ↔ _
  rw [and_iff_right rfl]
  rw [show (blocks B).src e=Stage.home B.next.placement (hop ((coarse).graph.src e)) by rfl,
      show (blocks B).dst e=Stage.home B.next.placement (hop ((coarse).graph.dst e)) by rfl,named_home,named_home]
  rfl

theorem peer_word_range (e : (coarse).graph.Edge) (x y : ℕ) (seen : rawPeer B e x y) :
    x < Fintype.card input.V*shelf ∧ y < Fintype.card input.V*shelf := by
  rcases (peer_words B e x y).mp seen with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> exact ⟨(rank _).isLt,(rank _).isLt⟩

theorem padded_peer_words (e : (coarse).graph.Edge) {H : ℕ} (pad : Fintype.card input.V ≤ H)
    (x y : ℕ) :
    let named:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb pad))
    rawPeer B e x y ↔
      (((named ((blocks B).src e).1.2).val=x ∧ (named ((blocks B).dst e).1.2).val=y) ∨
       ((named ((blocks B).dst e).1.2).val=x ∧ (named ((blocks B).src e).1.2).val=y)) :=
  peer_words B e x y

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
