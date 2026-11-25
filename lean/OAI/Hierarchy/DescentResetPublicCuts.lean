import OAI.Hierarchy.DescentPhysicalSheetRoom
import OAI.Hierarchy.DescentResetCanvasIngress

namespace OAI
/-! Monotonicity of all memory regions traversed by the fixed reset program. -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentSIMDLookup DescentResetDenseOperand
noncomputable section
set_option quotPrecheck false

structure ResetOutput.Cuts (v : ResetOutput) (b : ℕ) : Prop where
  middle : b≤v.middle.stop b
  actors : v.middle.stop b≤v.actorEnd b
  trunk : v.actorEnd b≤v.trunkEnd b
  mass : v.trunkEnd b≤v.massEnd b
  joint : v.massEnd b≤v.jointEnd b
  privateEnd : v.jointEnd b≤v.privateEnd b
  «meta» : v.privateEnd b≤v.sheets.metaEnd (v.remap b).endAddress
  originals : v.sheets.metaEnd (v.remap b).endAddress≤v.sheetsStart b
  candidates : v.sheetsStart b≤v.candidateEnd b
  scalar : v.candidateEnd b≤v.finalEnd b
  metadata : v.finalEnd b≤v.metadataEnd b

theorem ResetOutput.cuts (v : ResetOutput) (b : ℕ) : v.Cuts b := by
  constructor
  · rw [v.middle.translated];omega
  · rw [ResetOutput.actorEnd,v.actor.translated];omega
  · rw [ResetOutput.trunkEnd,v.front.trunk_shift];omega
  · rw [ResetOutput.massEnd,v.contactShape.translate];omega
  · rw [ResetOutput.jointEnd,JointAtlas.shift];omega
  · rw [ResetOutput.privateEnd,v.privateShape.translate];omega
  · simp only [CandidateSheets.metaEnd,CandidateSheets.masks,CandidateSheets.rank,
      DescentResetCandidateDate.Shape.endAddress,DescentResetCandidateDate.Shape.base,
      DescentResetCandidateDate.Shape.scratch,ResetOutput.remap,Layout.endAddress]
    omega
  · exact v.sheets.meta_before_original _
  · unfold ResetOutput.candidateEnd ResetOutput.sheetsStart CandidateSheets.endAddress
      DescentResetCandidatePair.endAddress DescentResetCandidatePair.originalBase
    omega
  · obtain ⟨_,second,third⟩:=v.earlier b
    have cut:=v.rankPort_after b
    have first:v.candidateEnd b≤v.ticketEnd b:=by
      unfold ResetOutput.ticketEnd ResetOutput.pairEnd DescentResetSourceTicketPair.endAt
        DescentResetSourceTicketBank.endAddress DescentResetSourceTicketBank.start
      exact (((cut.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans
        (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    exact ((first.trans second).trans third).trans (v.final_ge b)
  · obtain ⟨fund,venue⟩:=v.complete_after b
    have one:v.fullEnd b≤v.roleEnd b:=by rw [ResetOutput.roleEnd,v.roleTransfer.translate];omega
    have two:v.roleEnd b≤v.classEnd b:=by rw [ResetOutput.classEnd,v.actorClass.translate];omega
    have three:v.classEnd b≤v.birthEnd b:=by rw [ResetOutput.birthEnd,v.birth.translate];omega
    have four:v.birthEnd b≤v.primitiveEnd b:=by rw [ResetOutput.primitiveEnd,v.primitive.translate];omega
    have five:v.primitiveEnd b≤v.metadataEnd b:=by rw [ResetOutput.metadataEnd,v.metadata.translate];omega
    omega

namespace PhysicalReset
variable (a : PhysicalReset) (floor : ℕ)
local notation "v" => a.successor
local notation "start" => a.stageStart floor
local notation "b" => a.rebased start

theorem entered_bounds {w : ℕ} (room : a.fullEnd floor<2^w) :
    floor≤(v).actorEnd b ∧ (v).actorEnd b<2^w ∧ (v).trunkEnd b<2^w ∧
    (v).massEnd b<2^w ∧ (v).jointEnd b<2^w ∧ (v).privateEnd b<2^w ∧
    (v).sheets.metaEnd ((v).remap b).endAddress<2^w ∧ (v).finalEnd b<2^w := by
  obtain ⟨before,setup,_⟩:=a.occupied start
  obtain ⟨p,q,r⟩:=a.ingress.order floor
  have enter:floor≤ start:=p.trans (q.trans r)
  obtain ⟨m,h,t,s,j,pv,«meta»,orig,canon,fin,tail⟩:=(v).cuts b
  change (v).metadataEnd b<2^w at room
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem DateInputs.program_order {entry w : ℕ} (u : a.DateInputs entry w) :
    let base:=a.rebased entry
    entry≤(v).middle.stop base ∧ (v).middle.stop base≤(v).actorEnd base ∧
      (v).actorEnd base≤(v).trunkEnd base ∧ (v).trunkEnd base≤(v).massEnd base ∧
      (v).massEnd base≤(v).jointEnd base ∧ (v).jointEnd base≤(v).privateEnd base ∧
      (v).privateEnd base≤u.masked.endAddress ∧ u.masked.endAddress≤(v).sheetsStart base ∧
      (v).sheetsStart base≤(v).finalEnd base := by
  intro base
  obtain ⟨m,h,t,s,j,pv,«meta»,orig,canon,fin,_⟩:=(v).cuts base
  have early:=a.occupied entry
  rw [u.masks_end]
  exact ⟨(early.1.trans early.2.1).trans m,h,t,s,j,pv,«meta»,orig,canon.trans fin⟩

end PhysicalReset
end
end Hierarchy.DescentDatedAddressBook

end OAI
