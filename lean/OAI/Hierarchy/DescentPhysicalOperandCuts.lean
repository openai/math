import OAI.Hierarchy.DescentResetControlCuts
import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentPhysicalResetOperandRoom

namespace OAI
/-! Later operand passes can read all physical stem, donor, rank and parent rows. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentResetMixedWordRAM DescentDyadicSpan
noncomputable section
set_option quotPrecheck false

variable (v : ResetOutput) (b : ℕ)
local notation "early" => v.actorEnd b
local notation "first" => v.operandFloor b
local notation "s" => v.sheets
local notation "r" => (v.remap b).endAddress

private theorem le_four_offsets (start x y z t : ℕ) : start ≤ start+x+y+z+t := by omega

theorem operands_after_front :
    (v.front.parent early).base+span v.front.newHosts≤first ∧
    v.jointEnd b≤first ∧ (s).stemSources.coord.endAddress ((s).metaEnd r)≤first ∧
    v.candidateEnd b≤first ∧ v.operandStart b≤v.finalEnd b := by
  obtain ⟨_,_,trunk,mass,joint,private_,«meta»,orig,canon,_,_⟩:=v.cuts b
  have before:=(v.control_address_bounds b).2.2.1
  have ticket : v.rankPortEnd b≤v.ticketEnd b:=by
    unfold ticketEnd pairEnd DescentResetSourceTicketPair.endAt DescentResetSourceTicketBank.endAddress
      DescentResetSourceTicketBank.start
    exact le_four_offsets _ _ _ _ _
  have render:v.rankEnd b≤v.controlFloor b:=by
    change v.rankEnd b≤DescentNextSignedWindow.Native.All.endAddress (v.fieldsEnd b) _ _ _ _ _ _
    unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentNextSignedWindow.Native.All.endAddress
    omega
  have candidate:=(((v.rankPort_after b).trans ticket).trans (v.earlier b).2.1).trans (render.trans before)
  have source:v.sheetsStart b≤first:=canon.trans candidate
  have side:v.jointEnd b≤first:=private_.trans («meta».trans (orig.trans source))
  have prior:=v.front.front_order early
  have parent:=prior.2.2.trans prior.2.1
  have trunkCut:v.front.mixed early≤v.trunkEnd b:=le_four_offsets _ _ _ _ _
  have coord:(s).stemSources.coord.endAddress ((s).metaEnd r)≤(s).coordinateEnd r:=Nat.le_add_right ..
  have printed:(s).coordinateEnd r≤(s).inputDonorsEnd r:=by rw [(s).donors_shift];omega
  have origEnd:(s).inputDonorsEnd r≤v.sheetsStart b:=by
    unfold sheetsStart CandidateSheets.originalEnd DescentResetOriginalSlots.finish CandidateSheets.original
      CandidateSheets.privateArgsEnd DescentUniformSlotOperands.stop DescentResetHaloBroadcast.endAt
      CandidateSheets.stemFormatEnd CandidateSheets.publicFormatEnd OriginalBooks.afterHeader CandidateSheets.donorEnd
    exact (le_four_offsets _ _ _ _ _).trans (le_four_offsets _ _ _ _ _)
  obtain ⟨file,columns⟩:=v.operand_order b
  exact ⟨parent.trans (trunkCut.trans (mass.trans (joint.trans side))),side,
    coord.trans (printed.trans (origEnd.trans source)),candidate,(file.trans columns).trans (v.final_ge b)⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
