import OAI.Hierarchy.DescentRegisteredPrimitiveCheckpoint
import OAI.Hierarchy.DescentPrimitiveDateLocalBounds
import OAI.Hierarchy.DescentNamedArgumentVolume
import OAI.Hierarchy.DescentSeedEpochRoom

namespace OAI
/-! The ordinary primitive fee on the original chosen date, with the same two physical population terms as the argument pages. -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
def primitiveLaneRate (t f g reset driftR : ℕ) :=
  let c:=primitiveLocalRate G t f g reset
  let base:=(NativePitch.FundedBase.public_rate G t f g reset).choose
  3+max (c+44*argumentDigitRate G t f g reset driftR base) (8+3*(6*c+4))
def primitiveChargeRate (t f g reset driftR : ℕ):=
  let c:=primitiveLocalRate G t f g reset
  25+3*(6*c+4)+primitiveLaneRate G t f g reset driftR+1
structure PrimitiveCalendar (op : RotorSpec) (t f g reset τ B drift degreeMax driftR h : ℕ) : Prop where
  available : 4*scale (Nat.log 2 h/(2*B)) (primitiveLaneRate G t f g reset driftR)≤h
  localRows : ∀fund i p degree seats (prior : DatePorts),
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset fund (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let d:=DonorDate.atDate G S g k i p
      let book:=atDate G S op g k i p (tail τ J) drift degree h seats prior
      let bank:=scale J (primitiveLocalRate G t f g reset)
      p≤h → degree≤degreeMax → prior.nodes≤S.retainedNodes → S.firstWidth G.b p≤h →
      d.degree+1≤bank ∧ d.cap≤bank ∧ 2^k≤bank ∧ S.retainedNodes≤bank ∧ prior.nodes≤bank ∧
        printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op≤bank ∧ book.vector.lows≤bank

theorem eventual_primitive_calendar (op : RotorSpec) (t f g reset τ B drift degreeMax driftR : ℕ)
    (margin : primitiveLaneRate G t f g reset driftR+2≤B) :
    ∀ᶠ h:ℕ in atTop,PrimitiveCalendar G op t f g reset τ B drift degreeMax driftR h:=by
  have pos : 0<B:=by omega
  filter_upwards [primitive_date_local G op t f g reset τ B drift degreeMax pos,
    DescentCompiler.TerminalScale.eventually_late 1 B pos,eventually_ge_atTop 1] with h rows deep large
  exact ⟨DescentDatedSeedStartup.epoch_room h B _ large margin deep,rows⟩
end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "feeMultiplier" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height




open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (op : RotorSpec) (frozen drift degree payload seats hostLanes : ℕ) (ports : DatePorts)
variable (old : ProtocolRAM.Bank) (ordinary : ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "v" => (books).onTicket ticket g frozen p f payload seats hostLanes old ordinary

open DescentDatedOperandReadPipeline
variable (stageFloor : ℕ)
local notation "entry" => (v).datedEntry ports stageFloor
local notation "other" => purchase ((v).withFundedArguments 0 entry).ticketReadGeometry
local notation "ext" => (v).argumentUnitFrom ports stageFloor
local notation "Y" => (v).registeredFrom ports stageFloor
local notation "Q" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "growth" => 2*(2^S.hostGain*S.radix)
local notation "Z" => NativePitch.incoming S k frozen p f payload ordinary (i+1)


open DescentOrdinaryPalette DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
set_option quotPrecheck false
local notation "Y₀" => (v).registeredEntry ports stageFloor
local notation "b₀" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "L₀" => (Y).paletteShape
local notation "date₀" => DonorDate.atDate G S g k i p
local notation "work₀" => Configuration.workUnit (date₀).degree k (date₀).cap ports.nodes S.retainedNodes b₀
local notation "save₀" => Configuration.returnUnit b₀ S.retainedNodes


include before tail cut in
theorem registered_primitive_purchase {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (grain : p≤payload) (seed : S.firstWidth G.b p≤payload) (pPos : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) :
    let J:=Nat.log 2 payload/(2*β)
    (L₀).Funding payload (scale J (OrdinaryBooks.primitiveLaneRate G t f g reset driftR)) ∧
      (Y).primitiveFactor ≤ scale J (25+3*(6*OrdinaryBooks.primitiveLocalRate G t f g reset+4)):=by
  intro J
  let c:=OrdinaryBooks.primitiveLocalRate G t f g reset
  let base:=(NativePitch.FundedBase.public_rate G t f g reset).choose
  let funds:=44*argumentDigitRate G t f g reset driftR base
  let e:=OrdinaryBooks.primitiveLaneRate G t f g reset driftR
  let u:=scale J e
  have mono {a b : ℕ} (ok:a≤b) : scale J a ≤ scale J b:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ok)
  have measured : S=stageNumbers G t J f g reset copies (TerminalScale.tail τ J):=schedule.trans (by rw [tailBits])
  have layout : k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  have sz:=cost.localRows copies i p degree seats ports
  dsimp only at sz
  rw [←measured,←layout,←tailBits] at sz
  obtain ⟨dg,cap,blocks,nodes,priorNodes,printed,lows⟩:=sz grain degreeRoom (DatePorts.ArchiveWidths.node_bound G S op archive) seed
  have factors:=registered_primitive_factor X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor J c dg cap blocks nodes priorNodes printed lows
  have first:=registered_base_width X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary grant schedule depth grain
  have full:=registered_width_at X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor grant schedule depth tailBits dr first degreeRoom grain seed
    (DatePorts.ArchiveWidths.node_bound G S op archive) slots archive.digits
  have sum : 2^k*(v).fundedMaxUnit ext ≤ scale J (c+funds):=(Nat.mul_le_mul blocks full).trans_eq (scale_mul ..)
  have head : 8*(2^k*(v).fundedMaxUnit ext)≤u:=by
    have eight : 8 ≤ scale J 3:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_left 3 (Nat.succ_pos J))
    apply ((Nat.mul_le_mul eight sum).trans_eq (scale_mul ..)).trans
    exact mono (by dsimp only [e,OrdinaryBooks.primitiveLaneRate,c,funds,base];omega)
  have wide : 4*(v).fundedMaxUnit ext*2^k≤payload:=by
    have bound:=cost.available
    have step : 4*(v).fundedMaxUnit ext*2^k≤8*(2^k*(v).fundedMaxUnit ext):=by
      calc
        _=4*(2^k*(v).fundedMaxUnit ext):=by ring
        _≤_:=Nat.mul_le_mul_right _ (by decide : 4≤8)
    exact step.trans (head.trans (by change 4*u≤payload at bound;omega))
  have units : 2^k*(v).fundedWorkingUnit ext≤u:=((v).source_density ext).2.le.trans head
  have pay : scale J (8+3*(6*c+4))≤u:=mono (by dsimp only [e,OrdinaryBooks.primitiveLaneRate,c];omega)
  have wPaid:=factors.2.1.trans pay
  have sPaid:=factors.2.2.trans pay
  have carry:=grant.census copies frozen p i g grain
  dsimp only at carry
  rw [←schedule,←depth] at carry
  have pricePos : 0<S.censusBits p:=by
    have positive:=Nat.clog_pos (by decide : 1<2) (show 1<p+1 by omega)
    unfold AtomSchedule.censusBits;omega
  have bound : 4*u≤payload:=cost.available
  have reality:=registered_primitive_funding X G S br ticket before tail cut op frozen drift degree payload seats
    hostLanes ports old ordinary stageFloor u pricePos carry wide units (by omega) (by omega) wPaid sPaid
  exact ⟨reality,factors.1⟩

include before tail cut in
theorem registered_primitive_charge {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (grain : p≤payload) (seed : S.firstWidth G.b p≤payload) (pPos : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (age : i<S.length) (positive : 0<S.hostSize i)
    (w ratio : ℕ) (bus : w≤ratio*payload) :
    let J:=Nat.log 2 payload/(2*β)
    invoice ((Y).primitiveUpdate stageFloor Y₀ ((v).registered_match ports stageFloor (Nat.le_max_left ..)) rfl w)*w≤
      ratio*scale J (OrdinaryBooks.primitiveChargeRate G t f g reset driftR)*(Y).rowVolume payload:=by
  intro J
  let c:=OrdinaryBooks.primitiveLocalRate G t f g reset
  let e:=OrdinaryBooks.primitiveLaneRate G t f g reset driftR
  let u:=scale J e
  have purchased:=registered_primitive_purchase X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary stageFloor grant cost schedule depth tailBits dr degreeRoom grain seed pPos archive slots
  have bill:=registered_primitive_invoice (radix:=radix) X G S ticket op frozen drift degree payload seats hostLanes ports old ordinary
    stageFloor J (25+3*(6*c+4)) e u w ratio age purchased.1 bus purchased.2 le_rfl (Nat.le_max_left ..)
  have locus:=ports.registered_section_population ticket op g frozen p f drift degree payload seats hostLanes old ordinary
    stageFloor schedule positive radix
  have inside : hostRows (S.hostSize i)*payload+hostRows (S.hostSize i)*S.groupCount i+
      DescentOrdinaryPrimitiveCheckpoint.Layout.control payload≤(Y).rowVolume payload:=by
    rw [←locus.donor.1,←locus.donor.2]
    dsimp only [PhysicalOrdinary.rowVolume,DescentOrdinaryPrimitiveCheckpoint.Layout.control]
    omega
  rw [←Nat.mul_add] at bill
  exact bill.trans (Nat.mul_le_mul_left _ inside)

include before tail cut in
theorem chosen_primitive_charge {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (bin sockets : ℕ) (openSocket : 0<sockets)
    (split : p=bin*(payload/(16*((sockets*(G.b^(S.rounds*S.height)*G.b))*bin)))) (pPos : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (age : i<S.length) (positive : 0<S.hostSize i)
    (w ratio : ℕ) (bus : w≤ratio*payload) :
    let J:=Nat.log 2 payload/(2*β)
    invoice ((Y).primitiveUpdate stageFloor Y₀ ((v).registered_match ports stageFloor (Nat.le_max_left ..)) rfl w)*w≤
      ratio*scale J (OrdinaryBooks.primitiveChargeRate G t f g reset driftR)*(Y).rowVolume payload:=by
  have seed : S.firstWidth G.b p≤payload:=by
    rw [split];exact S.split_first_width G.b payload bin sockets openSocket
  have grain:=S.grain_le_payload G.b p payload G.base_pos seed
  exact registered_primitive_charge X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor grant cost schedule depth tailBits dr degreeRoom grain seed pPos archive slots age positive w ratio bus

include before tail cut in
theorem selected_primitive_room {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (bin sockets : ℕ) (openSocket : 0<sockets)
    (split : p=bin*(payload/(16*((sockets*(G.b^(S.rounds*S.height)*G.b))*bin)))) (pPos : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (age : i<S.length) {w : ℕ}
    (entryRoom : (Y₀).Room Y stageFloor w) (endRoom : (Y).primitiveRoof ((Y).operandEnd stageFloor)<2^w) :
    (Y).PrimitiveRoom stageFloor Y₀ w ∧
      (L₀).Capacity ((Y).primitiveSources stageFloor Y₀ ((v).registered_match ports stageFloor (Nat.le_max_left ..)) rfl):=by
  have seed : S.firstWidth G.b p≤payload:=by
    rw [split];exact S.split_first_width G.b payload bin sockets openSocket
  have grain:=S.grain_le_payload G.b p payload G.base_pos seed
  have bought:=registered_primitive_purchase X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary stageFloor grant cost schedule depth tailBits dr degreeRoom grain seed pPos archive slots
  exact registered_primitive_rooms (radix:=radix) (X:=X) (G:=G) (S:=S) (ticket:=ticket) (op:=op) (frozen:=frozen)
    (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (hostLanes:=hostLanes) (ports:=ports)
    (old:=old) (ordinary:=ordinary) (stageFloor:=stageFloor) age (Nat.le_max_left ..) entryRoom bought.1 endRoom

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
