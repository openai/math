import OAI.Hierarchy.DescentDatedTicketSourceRoom
import OAI.Hierarchy.DescentDatedOriginalHeaderRoom

namespace OAI
/-! # Total native execution of an ordinary ticket preparation on every input memory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentRawCablePanel DescentHaloWalkRAM
open DescentSIMDLookup DescentSharedCableNames DescentPackedZip DescentOrdinaryAtomFieldRAM
open DescentOrdinaryOriginMask DescentPackedActorMask DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor w : ℕ)
variable (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "l₀" => v.resolver
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "g₀" => v.ticketReadGeometry
local notation "d" => v.operandShortBits
local notation "M" => (l₀).lanes
local notation "N" => (l₀).nodes
local notation "routed₀" => v.routedStart floor
local notation "port₀" => v.originPortEnd floor
local notation "mouth₀" => v.originMouthEnd floor
local notation "old₀" => v.operandOldHeaderStart floor
local notation "new₀" => v.operandMouthHeaderStart floor
local notation "retile₀" => v.operandHeaderEnd floor
local notation "cast₀" => v.headTransferEnd floor
local notation "first₀" => v.operandRootBase floor
local notation "end₀" => v.preparedUntil floor

/-- Each component is a concrete physical input bank, extent, or word inequality.
In particular every premise is independent of the input memory. -/
structure TicketAdmission (pg : Fin (7*v.vector.operands)) : Prop where
  mask : ∀low,(DescentOrdinaryOriginMask.mask (((A.directory v floor mat).refs pg) low)).Fits w routed₀
  chip : (A.chipBank v floor).Fits w port₀
  groups : v.bornBook.groups=v.vector.groups*v.vector.radix
  lanes : 0<v.vector.lanes
  radix : 0<v.vector.radix
  refs : ∀arg low,((v.mouthRef A mat arg low).expr v.bornBook.hosts).inputEnd≤port₀
  panel : A.venue.panel.base+A.venue.panel.size ≤ mouth₀
  capacity : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size
  bits : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2
  prior : PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree (v.donorEnd floor)≤v.operandPathStart floor
  wide : ∀key,(v.wideHead floor c key).Fits w retile₀
  narrow : ∀key,(v.narrowHead floor key).Fits w retile₀
  sortedRoster : (A.ports v floor).roster.Fits w first₀

theorem header_dictionary_step (m : Memory w) (space : retile₀<2^w) :
    Step old₀ retile₀ (v.operandHeaderPhase floor w) m :=by
  let one:=previousHeaderPhase ((l₀).size+2) N M old₀ w
  let mid:=one.image m
  let two:=previousHeaderPhase v.bornBook.bits N M new₀ w
  have second : new₀≤retile₀:=Nat.le_add_right ..
  have oneRun:=ScalarOperand.header_dictionary ((l₀).size+2) N M old₀ m (second.trans_lt space)
  have twoRun:=ScalarOperand.header_dictionary v.bornBook.bits N M new₀ mid space
  have a : Step old₀ new₀ one m:=⟨Nat.le_add_right ..,oneRun.1,ROM.frame _ _ _ m⟩
  have b : Step new₀ retile₀ two mid:=⟨second,twoRun.1,ROM.frame _ _ _ mid⟩
  exact a.thenStep b

theorem ticket_preparation_trace (blocks : (l₀).blocks=(e₀).blocks)
    (pg : Fin (7*v.vector.operands)) (admit : v.TicketAdmission floor w c A mat pg) (space : end₀<2^w) (m : Memory w) :
    (Step routed₀ end₀ (v.nativeTicketPreparation floor w c A mat shape blocks pg) m ∧
      ∀j f,(v.nativeTicketExpr floor c A mat shape blocks j f).Fits w end₀) ∧
    ∀i,i<v.originPortFloor floor → (v.nativeTicketPreparation floor w c A mat shape blocks pg).image m i=
      v.originChart.image ((A.directory v floor mat).refs pg) routed₀ m i :=by
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=v.ticket_source_order floor
  have before:=r₉.trans_lt space
  have castRoom:=r₈.trans_lt before
  have headerRoom:=r₇.trans_lt castRoom
  have oldRoom:=r₅.trans_lt (r₆.trans_lt headerRoom)
  have mouthRoom:=r₄.trans_lt oldRoom
  let orig:=(A.directory v floor mat).refs pg
  let origin:=v.originPrefix floor d w orig
  let mouth:=v.originPrefixMouth floor w A mat
  let head:=v.originAndMouth floor w A mat d orig
  let left:=v.operandBeforeHeaders floor w A
  let books:=v.operandHeaderPhase floor w
  let change:=v.headTransferPhase floor c w
  let convert:=DescentDatedOperandCasts.phase v.operandWidth d M cast₀ w
  let m₀:=head.image m
  let m₁:=left.image m₀
  let m₂:=books.image m₁
  let m₃:=change.image m₂
  let m₄:=convert.image m₃
  have originRun:=v.originPrefix_run floor d w orig m admit.mask (r₃.trans_lt mouthRoom)
  have first : Step routed₀ port₀ origin m:=⟨r₁.trans r₂,originRun.1,originRun.2⟩
  have mouthRun:=v.originPrefixMouth_any floor A mat (origin.image m) admit.chip admit.groups admit.lanes admit.radix admit.refs mouthRoom
  have second : Step port₀ mouth₀ mouth (origin.image m):=⟨r₃,mouthRun.1,mouthRun.2⟩
  have third:=v.original_header_step floor A m₀ admit.panel admit.capacity admit.bits admit.prior oldRoom
  have fourth:=v.header_dictionary_step floor w m₁ headerRoom
  have transfer:=v.head_transfer_any floor c m₂ admit.wide admit.narrow castRoom
  have fifth : Step retile₀ cast₀ change m₂:=⟨r₇,transfer.1,transfer.2⟩
  have casts:=DescentDatedOperandCasts.any v.operandWidth d M before m₃
  have sixth : Step cast₀ first₀ convert m₃:=⟨r₈,casts.1,casts.2⟩
  have inputs:=v.native_source_room floor c A mat shape blocks before
  let pa:=v.operandPathStart floor
  let ra:=v.operandRankStart floor
  have paRank:=DescentDatedSourcePathDirectory.paths_fit_hosts (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree pa
  have rankOld : ra≤old₀:=Nat.le_add_right ..
  have paFirst : pa≤first₀:=(Nat.le_add_right ..).trans (paRank.trans (rankOld.trans (r₅.trans (r₆.trans (r₇.trans r₈)))))
  have source:=(DescentDatedSourcePathDirectory.native_header_room (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree
    (v.donorEnd floor) pa w admit.prior (paRank.trans_lt (rankOld.trans_lt ((r₅.trans (r₆.trans (r₇.trans r₈))).trans_lt before)))).2.1
  have vis : (v.operandRanks floor).endpoints.Fits w first₀:=⟨source.1,source.2.1,source.2.2.trans paFirst⟩
  have last:=SortedInput.program_total (g₀) (v.nativeTicketSources floor c A mat shape blocks) (e₀).oldHosts v.materialPitch
    (v.operandRanks floor).endpoints (A.ports v floor).roster m₄ inputs vis admit.sortedRoster space
  have suffix:=((((third.thenStep fourth).thenStep fifth).thenStep sixth).thenStep last.1)
  refine ⟨⟨(first.thenStep second).thenStep suffix,last.2⟩,?_⟩
  have port:=DescentOperandFamilyBook.any (DescentOrdinaryOriginPorts.law v.originChart d)
    v.vector.lanes (v.originPortFloor floor) (v.originChart.image orig routed₀ m) (r₃.trans_lt mouthRoom)
  intro i early
  have toPort : v.originPortFloor floor≤port₀:=Nat.le_add_right ..
  exact (suffix.frame i (.inl ((early.trans_le toPort).trans_le r₃))).trans
    ((second.frame i (.inl (early.trans_le toPort))).trans (port.2.2.1 i (.inl early)))

theorem ticket_preparation_any (blocks : (l₀).blocks=(e₀).blocks)
    (pg : Fin (7*v.vector.operands)) (admit : v.TicketAdmission floor w c A mat pg) (space : end₀<2^w) (m : Memory w) :
    Step routed₀ end₀ (v.nativeTicketPreparation floor w c A mat shape blocks pg) m ∧
      ∀j f,(v.nativeTicketExpr floor c A mat shape blocks j f).Fits w end₀ :=
  (v.ticket_preparation_trace floor w c A mat shape blocks pg admit space m).1

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
