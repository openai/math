import OAI.Hierarchy.DescentResetPeerFamilySupport
import OAI.Hierarchy.DescentResetPeerProgram
import OAI.Hierarchy.DescentResetTrunkMeta
import OAI.Hierarchy.DescentContactPreviousEnds
import OAI.Hierarchy.DescentResetHubRectangle
import OAI.Hierarchy.DescentResetLocalRosterPrice

namespace OAI
/-! # The measured previous neighbor roster covers every raw reset contact -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup DescentSortedRoster ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "height" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) height).card
local notation "Vnew" => ↥(ResetInput.commonNames B.reset B.terminals)
local notation "A" => input.placement
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex

def oldParent (v : Vnew) : input.V := B.frame.host.symm (position (Z).graph v.val)

private theorem same_parent_root (e : (coarse).graph.Edge)
    (same : receiverRoot B ((blocks B).src e)=receiverRoot B ((blocks B).dst e)) :
    oldParent B ((Z).placed T ((coarse).graph.src e))=oldParent B ((Z).placed T ((coarse).graph.dst e)) := by
  obtain ⟨left,right⟩:=endpoint_root B e
  exact congrArg B.frame.host.symm (congrArg Prod.fst ((left.symm.trans same).trans right))

private theorem contact_owner (c : (Z).placement.Contact) (s : Bool) :
    oldParent B ((Z).placed T (ends (coarse).graph s (contactParent B c)))=
        B.frame.host.symm ((Z).rootVertex T ((Z).placement.owner s c)) := by
  obtain ⟨left,right⟩:=endpoint_root B (contactParent B c)
  have base:=contact_endpoint_root B c s
  cases s
  · exact congrArg B.frame.host.symm (congrArg Prod.fst (left.symm.trans base))
  · exact congrArg B.frame.host.symm (congrArg Prod.fst (right.symm.trans base))

private theorem old_reach_edge (e : (coarse).graph.Edge) (s : Bool) :
    let parent:=fun side=>oldParent B ((Z).placed T (ends (coarse).graph side e))
    parent s=parent (!s) ∨ parent (!s)∈(A).mutual (parent s) := by
  dsimp only
  have self (q₀ : (coarse).graph.Edge)
      (eqn : oldParent B ((Z).placed T ((coarse).graph.src q₀))=oldParent B ((Z).placed T ((coarse).graph.dst q₀))) :
      oldParent B ((Z).placed T (ends (coarse).graph s q₀))=oldParent B ((Z).placed T (ends (coarse).graph (!s) q₀)) := by
    cases s
    · exact eqn
    · exact eqn.symm
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
  rcases tag with ⟨side,j⟩|t|c|x
  · obtain ⟨left,right⟩:=stem_receiver_root B side j
    exact Or.inl (self _ (same_parent_root B _ (left.trans right.symm)))
  · have «meta»:=trunk_host_words B t
    apply Or.inl (self _ ?_)
    exact (congrArg (fun node => B.frame.host.symm (position (Z).graph node)) «meta».1.1).trans
      (congrArg (fun node => B.frame.host.symm (position (Z).graph node)) «meta».1.2).symm
  · apply Or.inr
    change oldParent B ((Z).placed T (ends (coarse).graph (!s) (contactParent B c)))∈
      (A).mutual (oldParent B ((Z).placed T (ends (coarse).graph s (contactParent B c))))
    rw [contact_owner,contact_owner]
    exact contact_previous_near B c s
  · obtain ⟨left,right⟩:=private_endpoint_roots B x
    exact Or.inl (self _ (same_parent_root B _ (left.trans right.symm)))

theorem old_reach (v u : Vnew) (near : u∈(Z).emittedNear T v) :
    oldParent B v=oldParent B u ∨ oldParent B u∈(A).mutual (oldParent B v) := by
  obtain ⟨e,inc⟩:=(Finset.mem_filter.mp near).2
  rcases inc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact old_reach_edge B e false
  · exact old_reach_edge B e true

theorem candidate_coverage {H D₀ : ℕ} (previous : Fintype.card input.V ≤ H)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (issued : ∀v u : input.V,u∈(A).mutual v →
      ∃j,peers ((input.vertex v).castLE previous) j=some ((input.vertex u).castLE previous))
    (v u : Vnew) (near : u∈(Z).emittedNear T v) :
    let rank:=(Z).rawHostRank T ((vertex).trans (Fin.castLEEmb previous))
    ∃j,Candidates.candidate peers (rank v) j=some (rank u) := by
  dsimp only
  let tags:=(Z).hostFields T ((vertex).trans (Fin.castLEEmb previous))
  apply Candidates.cover peers (tags v).1 (tags u).1 (tags v).2 (tags u).2
  rcases old_reach B v u near with eqn|edge
  · exact Or.inl (congrArg (fun a=>(input.vertex a).castLE previous) eqn)
  · exact Or.inr (issued _ _ edge)

/-- The number of candidate shapes is determined by the immutable reset board
and schedule. It has no factor equal to the number of old high groups. -/
theorem peer_shelf_bound :
    shelf ≤ (2*((2^n+1)+((2*h+4)*2^n+(2^n+1)*2^(height+1))))*2^(k+1) := by
  rw [B.public_hub_slots]
  exact roster_bound ctl.board k height

/-- Exact fixed capacity of the hardware table on this chronological date. -/
theorem peer_span_calendar (start H D₀ b M : ℕ) :
    Program.endAddress start H shelf D₀ (totalLocal B) b M =
      Program.endAddress start H (DescentDenseHostOrder.roster ctl.board k height).card D₀
        (DescentResetLocalRoster.publicSlots ctl.board height k input.placement.cap) b M := by
  rw [B.public_hub_slots,local_roster_exact]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
