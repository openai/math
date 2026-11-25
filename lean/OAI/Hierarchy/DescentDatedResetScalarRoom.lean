import OAI.Hierarchy.DescentResetControlRegisterRun
import OAI.Hierarchy.DescentPrivateMaskRate
import OAI.Hierarchy.DescentContactOutputRate
import OAI.Hierarchy.DescentContactMaskRate
import OAI.Hierarchy.DescentDatedOperandSetupRate
import OAI.Hierarchy.DescentDatedCandidateFrontRate
import OAI.Hierarchy.DescentDatedCandidateSheetRate
import OAI.Hierarchy.DescentDatedPhysicalReset

namespace OAI
/-! # Deriving the full attained reset extent solely from its native scalar and word formats -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty.PackedFlow.Canvas DescentPackedFlowPublication DescentPlainTerminal.Suffix Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} (s : ∀h,ι h→PhysicalReset) (base : ∀h,ι h→ℕ)
local notation "U" => (fun h i=>(s h i).successor)
local notation "B" => (fun h i=>(s h i).successor.middle)
local notation "A" => (fun h i=>(s h i).successor.receiver)

/-- All geometries and thresholds here are actual dimension counts or word-field apertures.
The absolute stage end and the total output length are computed by the original machine. -/
structure ScalarRoom where
  controlDigits : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,let c:=((U) h i).controlRegisters;c.bits+c.dims.lanes≤K*h
  setup : DescentResetOperandSetup.Chart.ScalarRoom (fun h i=>(U h i).setup)
  actor : ActorSetup.ScalarRoom (fun h i=>(U h i).actor)
  jointDigits : Bounded (fun h i=>2^((U h i).sheets.metaBits))
  privateViews : DescentPrivateMaskDeck.Shape.ScalarRoom (fun h i=>(U h i).privateShape)
  contactOutput : DescentContactOutputShape.Shape.ScalarRoom (fun h i=>(U h i).contactShape)
  candidatesFront : CandidateFront.ScalarRoom (fun h i=>(U h i).front)
  candidatesSheets : CandidateSheets.ScalarRoom (fun h i=>(U h i).sheets)
  canvas : Placement.ScalarRoom (fun h i=>(s h i).chart (base h i)) (fun h i=>(s h i).payload) (fun h i=>(s h i).gain)
  radix : Bounded (fun h i=>2^(s h i).k)
  axes : Bounded (fun h i=>2^((s h i).high+(s h i).low))
  initialBook : ∀ᶠ h:ℕ in atTop,∀i,let v:=s h i;Book.width v.bits (2^v.k) v.short*v.lanes≤v.payload
  groups : Bounded (fun h i=>(s h i).groups)
  lanes : Bounded (fun h i=>2^(s h i).e)
  reblock : ∀ᶠ h:ℕ in atTop,∀i,let v:=s h i;v.re+v.field*(2^v.re*2^v.e)≤v.payload/2
  weighted : StencilBook.ScalarRoom (fun h i=>((B) h i).stencil)
  oldBlocks : Bounded (fun h i=>((B) h i).oldBlocks)
  signedLanes : Bounded (fun h i=>((B) h i).signedLanes)
  signedRatio : Bounded (fun h i=>((B) h i).signedRatio)
  retileKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let m:=(B) h i;m.signedBits*(m.signedRatio*m.signedLanes)≤K*h
  signedPorts : Bounded (fun h i=>((B) h i).signedPorts)
  signedHosts : Bounded (fun h i=>((B) h i).signedHosts)
  signedDimension : Bounded (fun h i=>((B) h i).high+((B) h i).low)
  signedHigh : Bounded (fun h i=>2^((B) h i).high)
  signedWord : ∀ᶠ h:ℕ in atTop,∀i,let v:=(B) h i;(v.signedBits+v.signedBits)*2^v.low≤(s h i).payload/2
  signedMatrix : ∀ᶠ h:ℕ in atTop,∀i,let v:=(B) h i;(v.high+v.low)*(v.high+v.low)≤(s h i).payload/2
  rootHosts : Bounded (fun h i=>((B) h i).rootHosts)
  rootGroups : Bounded (fun h i=>((B) h i).rootGroups)
  rootLanes : Bounded (fun h i=>((B) h i).rootLanes)
  rootBlocks : Bounded (fun h i=>2^((B) h i).rootDepth)
  rootShapes : Bounded (fun h i=>((B) h i).rootShapes)
  rootField : Bounded (fun h i=>2^((B) h i).rootField)
  rootLawWidth : Bounded (fun h i=>((B) h i).rootLawWidth)
  rotorBins : Bounded (fun h i=>2^((B) h i).rotorBits)
  degrees : Bounded (fun h i=>((B) h i).rootDegree)
  blocks : Bounded (fun h i=>((A) h i).blocks)
  capacity : Bounded (fun h i=>((A) h i).capacity)
  packedLanes : Bounded (fun h i=>((A) h i).lanes)
  receiverHosts : Bounded (fun h i=>((A) h i).hosts)
  receiverGroups : Bounded (fun h i=>((A) h i).groups)
  candidates : Bounded (fun h i=>((A) h i).candidates)
  «fields» : Bounded (fun h i=>((A) h i).fields)
  nodes : Bounded (fun h i=>((U) h i).nodes)
  argumentSlots : Bounded (fun h i=>((U) h i).argumentSlots)
  transfer : DescentRetainedHomeMover.Layout.ScalarRoom (fun h i=>(U h i).roleTransfer)
  birth : DescentPrimitiveBirth.Layout.ScalarRoom (fun h i=>(U h i).birth)
  primitive : DescentResetPrimitiveCheckpoint.Shape.ScalarRoom (fun h i=>(U h i).primitive)
  metadata : MetadataReturn.ScalarRoom (fun h i=>((U) h i).metadata)
  funded : DescentFundedCensus.Setup.ScalarRoom (fun h i=>((U) h i).funded)
  venue : ResetVenue.ScalarRoom (fun h i=>((U) h i).venue)
  nodeKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let u:=(U) h i;let a:=u.receiver;(u.nodeBits*u.nodes+u.nodeBits)*a.lanes≤K*h
  keepDigits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,((U) h i).setup.fieldBits*((U) h i).receiver.lanes≤K*h
  rankKey : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=(U) h i; (v.assemblerBits*5+v.assemblerBits*5)*v.receiver.lanes≤K*h
  dictionaries : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,
    let m:=(B) h i;let a:=(A) h i;let u:=(U) h i
    (m.signedBits*m.oldBlocks+m.signedBits)*m.signedLanes≤K*h ∧ m.projectBits*m.rootLanes≤K*h ∧
    (8*a.signedBits+a.signedBits)*a.lanes≤K*h ∧ (a.queryBits+a.signedBits)*a.lanes≤K*h ∧
    (u.ticketBits*5+u.ticketBits*5)*a.lanes≤K*h ∧ (u.assemblerBits*7+u.assemblerBits)*a.lanes≤K*h ∧
    (u.assemblerBits*7+u.sourceWordBits)*a.lanes≤K*h ∧ (DescentResetSourceSeekRAM.keyBits 4 a.candidates+u.sourceValueBits)*a.lanes≤K*h

theorem scalar_increment (r : ScalarRoom s base) :
    Bounded (fun h i=>(s h i).endAddress (base h i)-base h i) := by
  obtain ⟨P,p⟩:=r.canvas.payload
  have half : Bounded (fun h i=>2^((s h i).payload/2)) :=
    Bounded.pow_of_linear (K:=P) (p.mono fun h hh i=>(Nat.div_le_self ..).trans (hh i))
  obtain ⟨K,hw⟩:=r.dictionaries
  have old:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).1)
  have retile:=ResetMiddle.retile_rate (B) r.signedHosts r.rootGroups r.signedLanes r.signedPorts r.oldBlocks r.signedRatio r.retileKey
  have signed:=ResetMiddle.signed_span (B) (fun h i=>(s h i).payload)
    r.oldBlocks old retile (r.signedPorts.mul r.signedHosts) r.signedDimension r.signedHigh half r.signedWord r.signedMatrix
  have headers:=root_header_rate r.rootBlocks r.rotorBins r.degrees r.rootHosts r.rootGroups r.rootLanes r.rootShapes r.rootField r.rootLawWidth
  have picked:=ResetMiddle.geometric_rate (B) r.weighted signed r.rootHosts r.rootGroups r.rootLanes
    r.rootBlocks r.rotorBins r.degrees r.signedPorts headers ⟨K,hw.mono fun h hh i=>(hh i).2.1⟩
  have saved:=PublicOutput.width_rate (A) r.blocks r.capacity r.packedLanes r.receiverHosts r.receiverGroups
    r.candidates r.fields ⟨K,hw.mono fun h hh i=>⟨(hh i).2.2.1,(hh i).2.2.2.1⟩⟩
  have actorBound:=ActorSetup.rate _ r.actor
  have fr:=CandidateFront.rate _ r.candidatesFront
  have mass:=DescentContactOutputShape.Shape.rate _ r.contactOutput
  have masks:=DescentPrivateMaskDeck.Shape.rate _ r.privateViews
  have sh:=CandidateSheets.rate _ r.candidatesSheets
  have sr:=r.candidatesSheets
  have rails : Bounded (fun h i=>DescentSIMDLookup.chunks (U h i).sheets.groups (U h i).sheets.lanes) :=
    (sr.groups.add sr.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have raw:=(r.candidatesFront.oldHosts.mul r.candidatesFront.shapes).padded
  have remap:=((Bounded.const 2).mul (sr.hosts.mul rails).padded).add raw
  have joints:=JointAtlas.rate sr.hosts (r.candidatesFront.oldHosts.mul r.candidatesFront.shapes) sr.groups sr.lanes r.jointDigits
  have arrived : Bounded (fun h i=>(U h i).candidateEnd 0) := by
    apply (((((((picked.add actorBound).add fr).add mass).add joints).add masks).add remap).add sh).of_le
    intro h i
    let u:=U h i
    change u.candidateEnd 0≤_
    rw [ResetOutput.candidateEnd,u.sheets.shift]
    change u.privateShape.endAddress (JointAtlas.endAddress (u.contactShape.endAddress (u.front.trunkEnd (u.actor.directoryEnd (u.middle.stop 0)))) _ _ _ _ _)+(u.remap 0).size+u.sheets.endAddress 0≤_
    rw [u.privateShape.translate,JointAtlas.shift,u.contactShape.translate,u.front.trunk_shift,u.actor.translated]
    rfl
  have ports : Bounded (fun h i=>(U h i).rankPortEnd 0) :=by
    apply (arrived.add (DescentRankPortChart.bounded sr.hosts sr.groups sr.lanes)).of_le
    intro h i
    change DescentRankPortChart.endAddress _ _ _ _≤_
    rw [DescentRankPortChart.shift]
  have prepared:=DescentResetOperandSetup.Chart.rate _ r.setup
  have registers:=DescentResetControlRegisters.Chart.rate (fun h i=>(U h i).controlRegisters) r.venue.actor r.controlDigits
  obtain ⟨N,keepDigits⟩:=r.keepDigits
  have keep:=((Bounded.const (ι:=ι) 1).mul ((Bounded.const 2).mul (Bounded.pow_of_linear (K:=N) keepDigits)))
  have out:=ResetOutput.width_rate (U) ports saved registers prepared keep r.blocks r.candidates r.receiverHosts r.receiverGroups
    r.packedLanes r.rankKey ⟨K,hw.mono fun h hh i=>(hh i).2.2.2.2⟩
  have full:=ResetOutput.node_rate (U) out r.nodes r.argumentSlots r.blocks r.receiverHosts r.receiverGroups r.packedLanes r.nodeKey
  exact actual_increment s base r.canvas r.radix r.axes r.initialBook r.groups r.lanes r.reblock (ResetOutput.metadata_rate (U) (ResetOutput.full_rate (U) full r.funded r.venue) r.transfer
      (DescentResetActorClass.Shape.rate (fun h i=>(U h i).actorClass) (r.candidatesFront.oldHosts.mul r.candidatesFront.shapes) sr.hosts sr.groups sr.lanes) r.birth r.primitive r.metadata)

theorem complete_increment
    (r : ScalarRoom s (fun h i=>(s h i).stageStart (base h i)))
    (input : DescentResetCanvasIngress.Layout.ScalarRoom (fun h i=>(s h i).ingress)) :
    Bounded (fun h i=>(s h i).fullEnd (base h i)-base h i) :=by
  have before:=DescentResetCanvasIngress.Layout.rate (fun h i=>(s h i).ingress) input
  have after:=scalar_increment s _ r
  apply (before.add after).of_le
  intro h i
  have start:=(s h i).ingress.translate (base h i)
  change (s h i).stageStart (base h i)=base h i+(s h i).ingress.endAddress 0 at start
  change (s h i).endAddress ((s h i).stageStart (base h i))-base h i≤_
  omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
