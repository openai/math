import OAI.Hierarchy.DescentResetRegisterExtent
import OAI.Hierarchy.DescentRankPortChartSpace
import OAI.Hierarchy.DescentResetControlRegisters
import OAI.Hierarchy.DescentPrimitiveBirthLayout
import OAI.Hierarchy.DescentResetActorClassRate
import OAI.Hierarchy.DescentRetainedHomeMoverLayout
import OAI.Hierarchy.DescentPrimitiveCheckpointShape
import OAI.Hierarchy.DescentPrivateMaskShape
import OAI.Hierarchy.DescentContactOutputShape
import OAI.Hierarchy.DescentDatedJointAtlas
import OAI.Hierarchy.DescentContactMaskShape
import OAI.Hierarchy.DescentDatedReturnMetadata
import OAI.Hierarchy.DescentDatedResetVenue
import OAI.Hierarchy.DescentFundedSetupRate
import OAI.Hierarchy.DescentResetOperandSetupChart
import OAI.Hierarchy.DescentDatedActorAperture
import OAI.Hierarchy.DescentDatedCandidateSheets
import OAI.Hierarchy.DescentResetDenseOperand
import OAI.Hierarchy.DescentResetSourceTicketPair
import OAI.Hierarchy.DescentResetSourceTicketBank
import OAI.Hierarchy.DescentResetSourceSeekRAM
import OAI.Hierarchy.DescentResetWindowRanksRAM
import OAI.Hierarchy.DescentResetNodeBooks
import OAI.Hierarchy.DescentResetWindowRankInput
import OAI.Hierarchy.DescentDatedResetMiddle
import OAI.Hierarchy.DescentDatedPublicOutput
import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # All targets from the original reset window through the successor's complete operand field book -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup DescentResetSignedScan Filter
noncomputable section
structure ResetOutput where
  middle : ResetMiddle
  actor : ActorSetup
  front : CandidateFront
  sheets : CandidateSheets
  receiver : PublicOutput
  setup : DescentResetOperandSetup.Chart
  funded : DescentFundedCensus.Setup
  venue : ResetVenue
  roleTransfer : DescentRetainedHomeMover.Layout
  birth : DescentPrimitiveBirth.Layout
  primitive : DescentResetPrimitiveCheckpoint.Shape
  metadata : MetadataReturn
  ticketBits : ℕ
  assemblerBits : ℕ
  nodes : ℕ
  argumentSlots : ℕ
  nodeBits : ℕ
  rootOutputBits : ℕ
namespace ResetOutput
variable (v : ResetOutput)

def sourceWordBits :=v.ticketBits
def sourceValueBits :=v.assemblerBits

/-- First address of the physical `RankedWindows.Layout` after the underlying candidate sheets. -/
def actorEnd (base : ℕ) :=v.actor.directoryEnd (v.middle.stop base)
def trunkEnd (base : ℕ) :=v.front.trunkEnd (v.actorEnd base)
def contactShape : DescentContactOutputShape.Shape :=
  ⟨v.front.donor,v.front.peer.shapes,v.sheets.groups,v.sheets.blocks,v.sheets.lanes,
    v.front.contact.outputBits,v.sheets.metaBits⟩
def massEnd (base : ℕ) :=v.contactShape.endAddress (v.trunkEnd base)
def jointEnd (base : ℕ) :=JointAtlas.endAddress (v.massEnd base) v.sheets.hosts v.front.peer.hosts v.sheets.groups v.sheets.lanes v.sheets.metaBits
def privateShape : DescentPrivateMaskDeck.Shape :=
  ⟨v.front.peer.oldHosts,v.front.peer.shapes,v.sheets.groups,v.sheets.blocks,v.front.oldLanes,v.sheets.lanes,
    v.front.wireCap,v.front.privateBits,v.sheets.metaBits,v.front.contact.residual,2^v.front.contact.n⟩
def privateEnd (base : ℕ) :=v.privateShape.endAddress (v.jointEnd base)
def remap (base : ℕ) : DescentResetDenseOperand.Layout :=
  ⟨v.privateEnd base,v.sheets.hosts,v.front.peer.hosts,chunks v.sheets.groups v.sheets.lanes⟩
def candidateEnd (base : ℕ) :=v.sheets.endAddress (v.remap base).endAddress

theorem candidate_shift (base : ℕ) : v.candidateEnd base=base+v.candidateEnd 0 := by
  have compose (f : ℕ → ℕ) (shift : ∀ x, f x=x+f 0) {x y : ℕ} (eqn : x=base+y) :
      f x=base+f y := by rw [shift x,shift y,eqn,Nat.add_assoc]
  have actor : v.actorEnd base=base+v.actorEnd 0 :=
    compose _ v.actor.translated (v.middle.translated base)
  have trunk : v.trunkEnd base=base+v.trunkEnd 0 := compose _ v.front.trunk_shift actor
  have mass : v.massEnd base=base+v.massEnd 0 := compose _ v.contactShape.translate trunk
  have joint : v.jointEnd base=base+v.jointEnd 0 :=
    compose _ (fun x => JointAtlas.shift x _ _ _ _ _) mass
  have privateEnd' : v.privateEnd base=base+v.privateEnd 0 :=
    compose _ v.privateShape.translate joint
  apply compose _ v.sheets.shift
  change v.privateEnd base+(v.remap base).size=base+(v.privateEnd 0+(v.remap 0).size)
  simp only [DescentResetDenseOperand.Layout.size,DescentResetDenseOperand.Layout.pitch,
    DescentResetDenseOperand.Layout.rawPitch,remap]
  rw [privateEnd',Nat.add_assoc]

theorem candidates_after_middle (base : ℕ) : v.middle.stop base≤v.candidateEnd base := by
  apply le_trans _ (v.sheets.room _)
  change v.middle.stop base≤v.privateShape.endAddress (JointAtlas.endAddress (v.contactShape.endAddress (v.front.trunkEnd (v.actor.directoryEnd (v.middle.stop base)))) _ _ _ _ _)+(v.remap base).size
  rw [v.privateShape.translate,JointAtlas.shift,v.contactShape.translate,v.front.trunk_shift,v.actor.translated]
  omega
def rankPortEnd (base : ℕ) :=DescentRankPortChart.endAddress (v.candidateEnd base) v.sheets.hosts v.sheets.groups v.sheets.lanes

theorem rankPort_shift (base : ℕ) : v.rankPortEnd base=base+v.rankPortEnd 0 :=by
  unfold rankPortEnd DescentRankPortChart.endAddress DescentRankPortChart.rosterEnd DescentScalarHaloPortROM.stop
  rw [v.candidate_shift base];omega

theorem rankPort_after (base : ℕ) : v.candidateEnd base≤v.rankPortEnd base :=by
  unfold rankPortEnd DescentRankPortChart.endAddress DescentRankPortChart.rosterEnd DescentScalarHaloPortROM.stop
  omega

def pairEnd (base : ℕ) :=DescentResetSourceTicketPair.endAt (v.rankPortEnd base) v.assemblerBits v.ticketBits v.receiver.lanes
def ticketEnd (base : ℕ) :=
  DescentResetSourceTicketBank.endAddress (v.pairEnd base) v.ticketBits v.receiver.lanes v.receiver.hosts v.receiver.groups v.receiver.blocks v.receiver.candidates
def seekEnd (base : ℕ) :=DescentResetSourceSeekRAM.endAddress (v.ticketEnd base) 4 v.receiver.candidates
  v.assemblerBits v.ticketBits v.assemblerBits v.receiver.lanes
def rankInput (base : ℕ) :=RankInput.endAddress (v.seekEnd base) v.assemblerBits v.receiver.lanes
def rankEnd (base : ℕ) :=
  Ranks.endAddress (v.rankInput base) v.receiver.blocks v.receiver.candidates v.assemblerBits v.receiver.lanes v.receiver.hosts v.receiver.groups
def fieldsEnd (base : ℕ) :=DescentResetFieldAssembler.endAddress (v.rankEnd base) v.assemblerBits v.receiver.lanes
def controlFloor (base : ℕ) :=v.receiver.rendered (v.fieldsEnd base)
def controlRegisters : DescentResetControlRegisters.Chart := ⟨v.venue.actorDims,v.setup.rotorBits⟩
def operandFloor (base : ℕ) :=v.controlRegisters.endAddress (v.controlFloor base)
def keepBase (base : ℕ) :=v.setup.endAddress (v.operandFloor base)
def keepWords :=1*(2*2^(v.setup.fieldBits*v.receiver.lanes))
def operandStart (base : ℕ) :=v.keepBase base+v.keepWords
def operandDictionaryEnd (base : ℕ) :=DescentOperandCandidateLookup.dictionaryEnd (2*v.receiver.candidates) v.receiver.queryBits v.receiver.signedBits
  v.receiver.lanes (v.operandStart base)
def endAddress (base : ℕ) :=DescentOperandCandidateLookup.Batch.outputEnd v.receiver.fields v.receiver.hosts v.receiver.groups v.receiver.lanes (v.operandDictionaryEnd base)

theorem scalar_original_extent (base : ℕ) : v.endAddress base=v.receiver.endAddress (v.fieldsEnd base)+v.controlRegisters.endAddress 0+v.setup.endAddress 0+v.keepWords :=by
  unfold endAddress operandDictionaryEnd operandStart keepBase
  rw [v.setup.affine (v.operandFloor base)]
  unfold operandFloor
  rw [v.controlRegisters.translated (v.controlFloor base)]
  unfold controlFloor PublicOutput.endAddress PublicOutput.operands DescentOperandCandidateLookup.dictionaryEnd
    DescentOperandCandidateLookup.Batch.outputEnd
  omega

abbrev scalarEnd (base : ℕ) :=v.endAddress base
def rangeLayout : DescentDatedPriorOperand.Layout :=
  ⟨v.receiver.blocks,v.nodes,v.argumentSlots,v.receiver.hosts,v.receiver.groups,v.receiver.lanes,v.nodeBits-2⟩

def nodeNames :=(7*v.argumentSlots)*v.receiver.blocks
def finalEnd (base : ℕ) :=DescentResetNodeBooks.endAddress (v.scalarEnd base) v.nodeNames
  v.nodes v.receiver.hosts v.receiver.groups v.nodeBits v.receiver.lanes

theorem final_ge (base : ℕ) : v.endAddress base≤v.finalEnd base := by
  obtain ⟨started, bounded⟩ := DescentResetNodeBooks.output_window v.rangeLayout (v.scalarEnd base) v.nodeBits
  exact (started.trans bounded).trans_eq (DescentResetNodeBooks.previous_limit v.rangeLayout (v.scalarEnd base) v.nodeBits)

theorem exact_span (base : ℕ) :
    let rows:=v.receiver.hosts*chunks v.receiver.groups v.receiver.lanes
    let page:=2^((v.ticketBits*5+v.ticketBits*5)*v.receiver.lanes)
    v.endAddress base=base+v.rankPortEnd 0+
      6*2^((v.assemblerBits*7+v.ticketBits)*v.receiver.lanes)+2*page+(v.receiver.blocks*v.receiver.candidates)*rows+2^(Nat.clog 2 rows)+
      v.receiver.candidates*2*2^((v.assemblerBits*7+v.sourceWordBits)*v.receiver.lanes)+
      (4*v.receiver.candidates)*2*2^((DescentResetSourceSeekRAM.keyBits 4 v.receiver.candidates+v.sourceValueBits)*v.receiver.lanes)+
      2*2^((v.assemblerBits*7+v.assemblerBits)*v.receiver.lanes)+4*2^((v.assemblerBits*5+v.assemblerBits*5)*v.receiver.lanes)+((v.receiver.blocks*3)*v.receiver.candidates)*2^(Nat.clog 2 rows)+
      32*2^((v.assemblerBits*7+v.assemblerBits)*v.receiver.lanes)+v.receiver.endAddress 0+v.controlRegisters.endAddress 0+v.setup.endAddress 0+v.keepWords := by
  dsimp only
  rw [v.scalar_original_extent,v.receiver.translate (v.fieldsEnd base)]
  unfold fieldsEnd DescentResetFieldAssembler.endAddress DescentResetFieldAssembler.width rankEnd rankInput RankInput.endAddress RankInput.width seekEnd DescentResetSourceSeekRAM.endAddress DescentResetSourceSeekRAM.addressEnd ticketEnd pairEnd DescentResetSourceTicketPair.endAt DescentResetSourceTicketPair.width sourceWordBits sourceValueBits
  simp only [Ranks.endAddress,Ranks.start,Ranks.headWords,Ranks.width,Ranks.count,DescentDyadicSpan.span,
    DescentResetSourceTicketBank.endAddress,DescentResetSourceTicketBank.start,DescentResetSourceTicketBank.span,
    v.rankPort_shift base]

theorem translated (base : ℕ) : v.endAddress base=base+v.endAddress 0 := by
  rw [v.exact_span base,v.exact_span 0]
  omega

theorem finalTranslated (base : ℕ) : v.finalEnd base=base+v.finalEnd 0 := by
  unfold finalEnd scalarEnd
  rw [DescentResetNodeBooks.affine (v.endAddress base),DescentResetNodeBooks.affine (v.endAddress 0),v.translated]
  omega

/-- The packed operand output stays available to the following stage while all previous
funded widths are regrouped and the new compact host, signed and census banks are issued. -/
def fundedEnd (base : ℕ) := v.funded.roof (v.finalEnd base)
def fullEnd (base : ℕ) := v.venue.endAddress (v.fundedEnd base)

theorem fullTranslated (base : ℕ) : v.fullEnd base=base+v.fullEnd 0 :=by
  rw [fullEnd,fullEnd,v.venue.translated (v.fundedEnd base),v.venue.translated (v.fundedEnd 0)]
  unfold fundedEnd
  rw [v.funded.shift (v.finalEnd base),v.funded.shift (v.finalEnd 0),v.finalTranslated base]
  omega

theorem complete_after (base : ℕ) : v.finalEnd base≤v.fundedEnd base ∧ v.fundedEnd base≤v.fullEnd base :=by
  have grow:=v.venue.after (v.fundedEnd base)
  exact ⟨v.funded.room _,(grow.1.trans grow.2.1).trans grow.2.2⟩

theorem full_rate {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)
    (prior : Bounded (fun h i=>(p h i).finalEnd 0))
    (setup : DescentFundedCensus.Setup.ScalarRoom (fun h i=>(p h i).funded))
    (venue : ResetVenue.ScalarRoom (fun h i=>(p h i).venue)) :
    Bounded (fun h i=>(p h i).fullEnd 0) :=by
  have old:=DescentFundedCensus.Setup.rate _ setup
  have last:=ResetVenue.extent_rate _ venue
  apply ((prior.add old).add last).of_le
  intro h i
  unfold fullEnd
  rw [(p h i).venue.translated]
  unfold fundedEnd
  rw [(p h i).funded.shift]

def roleEnd (base : ℕ) := v.roleTransfer.endAddress (v.fullEnd base)
def actorClass : DescentResetActorClass.Shape := ⟨v.front.peer.hosts,v.sheets.hosts,v.sheets.groups,v.sheets.lanes⟩
def classEnd (base : ℕ) :=v.actorClass.endAddress (v.roleEnd base)
def birthEnd (base : ℕ) :=v.birth.endAddress (v.classEnd base)
def primitiveEnd (base : ℕ) :=v.primitive.endAddress (v.birthEnd base)
theorem roleTranslated (base : ℕ) : v.roleEnd base=base+v.roleEnd 0 :=by
  rw [roleEnd,roleEnd,v.roleTransfer.translate (v.fullEnd base),v.roleTransfer.translate (v.fullEnd 0),
    v.fullTranslated base];omega
def metadataEnd (base : ℕ) :=v.metadata.endAddress (v.primitiveEnd base)
theorem classTranslated (base : ℕ) : v.classEnd base=base+v.classEnd 0 :=by
  rw [classEnd,classEnd,v.actorClass.translate (v.roleEnd base),v.actorClass.translate (v.roleEnd 0),
    v.roleTranslated base];omega
theorem birthTranslated (base : ℕ) : v.birthEnd base=base+v.birthEnd 0 :=by
  rw [birthEnd,birthEnd,v.birth.translate (v.classEnd base),v.birth.translate (v.classEnd 0),
    v.classTranslated base];omega
theorem primitiveTranslated (base : ℕ) : v.primitiveEnd base=base+v.primitiveEnd 0 :=by
  rw [primitiveEnd,primitiveEnd,v.primitive.translate (v.birthEnd base),v.primitive.translate (v.birthEnd 0),
    v.birthTranslated base];omega
theorem metadataTranslated (base : ℕ) : v.metadataEnd base=base+v.metadataEnd 0 :=by
  rw [metadataEnd,metadataEnd,v.metadata.translate (v.primitiveEnd base),v.metadata.translate (v.primitiveEnd 0),
    v.primitiveTranslated base];omega
theorem metadata_rate {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)
    (prior : Bounded (fun h i=>(p h i).fullEnd 0))
    (transfer : DescentRetainedHomeMover.Layout.ScalarRoom (fun h i=>(p h i).roleTransfer))
    (classes : Bounded (fun h i=>(p h i).actorClass.endAddress 0))
    (fresh : DescentPrimitiveBirth.Layout.ScalarRoom (fun h i=>(p h i).birth))
    (codes : DescentResetPrimitiveCheckpoint.Shape.ScalarRoom (fun h i=>(p h i).primitive))
    (room : MetadataReturn.ScalarRoom (fun h i=>(p h i).metadata)) :
    Bounded (fun h i=>(p h i).metadataEnd 0) :=by
  apply (((((prior.add (DescentRetainedHomeMover.Layout.rate _ transfer)).add classes).add (DescentPrimitiveBirth.Layout.rate _ fresh)).add (DescentResetPrimitiveCheckpoint.Shape.rate _ codes)).add (MetadataReturn.extent_rate _ room)).of_le
  intro h i
  rw [metadataEnd,(p h i).metadata.translate,primitiveEnd,(p h i).primitive.translate,birthEnd,(p h i).birth.translate,classEnd,(p h i).actorClass.translate,roleEnd,(p h i).roleTransfer.translate]

theorem earlier (base : ℕ) : v.middle.stop base≤v.ticketEnd base ∧
    v.ticketEnd base≤v.rankEnd base ∧ v.rankEnd base≤v.endAddress base := by
  have out:=v.receiver.occupied (v.fieldsEnd base)
  have rank : v.rankEnd base≤v.fieldsEnd base:=Nat.le_add_right ..
  refine ⟨?_,?_,rank.trans (((out.1.trans out.2.1).trans out.2.2).trans (by rw [v.scalar_original_extent];omega))⟩
  · have h:=(v.candidates_after_middle base).trans (v.rankPort_after base)
    apply h.trans
    unfold ticketEnd pairEnd DescentResetSourceTicketPair.endAt DescentResetSourceTicketBank.endAddress DescentResetSourceTicketBank.start
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  · unfold rankEnd Ranks.endAddress Ranks.start rankInput RankInput.endAddress seekEnd DescentResetSourceSeekRAM.endAddress DescentResetSourceSeekRAM.addressEnd
    omega

theorem width_rate {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)
    (middle : Bounded (fun h i=>(p h i).rankPortEnd 0))
    (final : Bounded (fun h i=>(p h i).receiver.endAddress 0))
    (control : Bounded (fun h i=>(p h i).controlRegisters.endAddress 0))
    (prepared : Bounded (fun h i=>(p h i).setup.endAddress 0))
    (keep : Bounded (fun h i=>(p h i).keepWords))
    (blocks : Bounded (fun h i=>(p h i).receiver.blocks))
    (slots : Bounded (fun h i=>(p h i).receiver.candidates))
    (hosts : Bounded (fun h i=>(p h i).receiver.hosts))
    (groups : Bounded (fun h i=>(p h i).receiver.groups))
    (lanes : Bounded (fun h i=>(p h i).receiver.lanes))
    (rankKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=p h i;(a.assemblerBits*5+a.assemblerBits*5)*a.receiver.lanes≤K*h)
    (field : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=p h i;
      (a.ticketBits*5+a.ticketBits*5)*a.receiver.lanes≤K*h ∧ (a.assemblerBits*7+a.assemblerBits)*a.receiver.lanes≤K*h ∧
      (a.assemblerBits*7+a.sourceWordBits)*a.receiver.lanes≤K*h ∧
      (DescentResetSourceSeekRAM.keyBits 4 a.receiver.candidates+a.sourceValueBits)*a.receiver.lanes≤K*h) :
    Bounded (fun h i=>(p h i).endAddress 0) := by
  obtain ⟨K,hw⟩:=field
  have page:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).1)
  have fields_:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).2.1)
  have header_:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).2.2.1)
  have payload_:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).2.2.2)
  obtain ⟨J,hr⟩:=rankKey
  have ranks_:=Bounded.pow_of_linear (K:=J) hr
  have batch : Bounded (fun h i=>chunks (p h i).receiver.groups (p h i).receiver.lanes) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=hosts.mul batch
  have rounded:=rows.padded
  have pre:=middle.add ((Bounded.const 6).mul header_)
  have archives:=(((pre.add ((Bounded.const 2).mul page)).add ((blocks.mul slots).mul rows)).add rounded)
  have seek:=(archives.add ((slots.mul (Bounded.const 2)).mul header_)).add
    ((((Bounded.const 4).mul slots).mul (Bounded.const 2)).mul payload_)
  have lookup:=(((seek.add ((Bounded.const 2).mul fields_)).add ((Bounded.const 4).mul ranks_)).add
    (((blocks.mul (Bounded.const 3)).mul slots).mul rounded))
  have upper:=(lookup.add ((Bounded.const 32).mul fields_)).add final
  apply (((upper.add control).add prepared).add keep).of_le
  intro h i
  rw [(p h i).exact_span]
  simp only [sourceWordBits,sourceValueBits,Nat.zero_add,Nat.le_refl]

theorem node_rate {ι : ℕ→Type*} (p : ∀h,ι h→ResetOutput)
    (scalar : Bounded (fun h i=>(p h i).endAddress 0)) (nodes : Bounded (fun h i=>(p h i).nodes))
    (arity : Bounded (fun h i=>(p h i).argumentSlots)) (blocks : Bounded (fun h i=>(p h i).receiver.blocks))
    (hosts : Bounded (fun h i=>(p h i).receiver.hosts)) (groups : Bounded (fun h i=>(p h i).receiver.groups))
    (lanes : Bounded (fun h i=>(p h i).receiver.lanes))
    (packed : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let u:=p h i;let a:=u.receiver;(u.nodeBits*u.nodes+u.nodeBits)*a.lanes≤K*h) :
    Bounded (fun h i=>(p h i).finalEnd 0) := by
  obtain ⟨K,hk⟩:=packed
  have rows:=hosts.mul ((groups.add lanes).of_le (y:=fun h i=>chunks (p h i).receiver.groups (p h i).receiver.lanes)
    fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have rounded:=(rows.add (Bounded.const 1)).padded
  have rom:=(nodes.add (Bounded.const 1)).mul (Bounded.pow_of_linear (K:=K) hk)
  have names:=((Bounded.const 7).mul arity).mul blocks
  exact ((scalar.add (rom.max' rounded)).add (names.mul rows)).add rounded

end ResetOutput
end
end Hierarchy.DescentDatedAddressBook

end OAI
