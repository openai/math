import OAI.Hierarchy.DescentNamedTailBooks
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentFundedTailDensity
import OAI.Hierarchy.DescentCalibratedIncomingVolume
import OAI.Hierarchy.DescentDonorCensusFloor

namespace OAI
/-! # Original named tail with the complete prior-register book and the real reserved root addresses -/
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
local notation "bits" => (fun _ : P=>s*1)
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

include before tail cut in
theorem registered_tail_invoice {t J reset M last driftR funds dest : ℕ}
    (schedule : S=stageNumbers G t J f g reset M last)
    (depth : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (dr : drift+1≤ scale J driftR) (live : 0<S.hostSize i) (args : ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (maxWidth : (v).fundedMaxUnit ext≤ scale J funds)
    (paid : 0<S.censusBits p) (paidFits : S.censusBits p≤(v).area.unit)
    (incoming : 0<Z ∧ Z≤payload/2 ∧ ∀H,H*chunks (S.groupCount (i+1)) Z*payload≤H*payload+H*S.groupCount (i+1)*scale J dest)
    (floor w ratio : ℕ) (B : StageVenueTail.Sources) (room : (Y).ResultRoom floor B w) (bus : w≤ratio*payload) :
    let radixR:=groupRate G t f g reset
    let laneR:=tailUnitRate (radixR+funds) (signedRates G t f g reset).amount dest
    let rate:=endRate (tailLayoutRate G t f g reset driftR laneR)
    2*scale J laneR≤payload →
      (Y).tailAmount floor w B room≤ratio*scale J rate*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload :=by
  intro radixR laneR rate wide
  let u:=scale J laneR
  have uPos : 0<u:=Nat.two_pow_pos _
  have kbits : 2^k≤ scale J radixR:=by
    rw [depth]
    exact Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have reserved : (2^k)*(v).fundedMaxUnit ext≤ scale J (radixR+funds):=(Nat.mul_le_mul kbits maxWidth).trans_eq (scale_mul ..)
  have actual:=ticket.selected_signed_rates schedule depth (hostRows (S.hostSize i)) (NativePitch.incomingHosts S (i+1))
    (S.groupCount (i+1)) payload
  have signed:=actual.1
  rw [signed_stage_eq X G S br ticket before tail cut (NativePitch.incomingHosts S (i+1))] at signed
  obtain ⟨oldPaid,signedPaid,nextPaid⟩:=tail_unit_rows reserved signed dest
  have rowU : scale J dest≤u:=nextPaid
  have areaDebit : (v).unit≤(2^k)*(v).fundedMaxUnit ext:=((v).source_density ext).1.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k))
  have areaU : (v).unit≤u:=areaDebit.trans ((Nat.le_mul_of_pos_left _ (by decide : 0<8)).trans oldPaid)
  have form : 4*(v).fundedMaxUnit ext*2^k≤payload:=by
    have b : 4*(v).fundedMaxUnit ext*2^k≤u:=(by
      have := Nat.mul_le_mul_right ((2^k)*(v).fundedMaxUnit ext) (by decide : 4≤8)
      calc
        _ = 4*((2^k)*(v).fundedMaxUnit ext):=by ring
        _ ≤ _:=this.trans oldPaid)
    omega
  have sr : 2*(Q).unit≤payload:=by change 4*(Q).unit≤u at signedPaid;omega
  have pu : 2^k*(v).fundedWorkingUnit ext≤u:=((v).source_density ext).2.le.trans oldPaid
  have metadata:=registered_tail_books X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary entry other schedule live args
  have post:=(v).funded_argument_bounds ext entry paid paidFits form
  have fill : payload≤((v).fundedClip ext).postPitch*u:=post.fill₂.trans (Nat.mul_le_mul_left _ pu)
  have shelves : (Y).ShelfRows u 1:=by
    obtain ⟨pos,budget,nodes,counts,args,joined,rows⟩:=(v).funded_shelf_rows entry other u uPos wide metadata.1 fill
    exact ⟨pos,budget,nodes,counts,args,joined,rows⟩
  obtain ⟨pos,small,rows⟩:=incoming
  have destination : (Y).venue.hosts*chunks (Y).venue.groups (Y).venue.lanes*payload≤(Y).venue.hosts*payload+(Y).venue.hosts*(Y).venue.groups*u:=
    (rows (Y).venue.hosts).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ rowU) _)
  have venue : (Y).venue.SourceRows payload u:=(v).funded_venue_rows entry g frozen p f hostLanes ext ordinary u
    rfl paid paidFits form sr signedPaid pu pos small destination
  have cost:=issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
  have cap:=signed_source_capacity X G S br ticket before tail cut
  have widths:=ticket.donorDate.matcher_widths 0 (show 0<ticket.donorDate.cap from by change 0<(A).cap;omega) (Nat.zero_le _)
  have cnt : (Y).countBits≤payload/2:=by
    have nativeBits : (v).area.shapeAt.outputBits≤DescentPacking.PackedMatch.SixBirths.unit (v).area.shapeAt:=(Nat.le_add_left ..).trans (Nat.le_max_left ..)
    have chunk : (v).area.unit*(v).area.lanesAt≤payload/2:=by
      change (v).area.unit * lanes payload (v).area.unit ≤ payload/2
      rw [Nat.mul_comm]
      exact lanes_fit payload (v).area.unit
    apply (Nat.mul_le_mul_right _ (nativeBits.trans ?_)).trans chunk
    change DescentPacking.PackedMatch.SixBirths.unit ticket.donorDate.matcher≤(v).unit
    rw [cost.2.1];exact widths.2.2.2.2
  have oldPos : 0<(v).unit:=paid.trans_le paidFits
  have oldWide : 2*(v).unit≤payload:=(Nat.mul_le_mul_left 2 areaU).trans wide
  have host:=ordinary_host_rectangle S (radix:=radix) live ticket.hubRows.choose
  have once : (Y).area.H≤S.hostSize i*2:=by
    change hostRows (S.hostSize i)≤_
    simpa only [Nat.mul_comm] using hostRows_double live
  let scale_:=scale J (tailLayoutRate G t f g reset driftR laneR)
  have priced:=(Y).tail_paid floor w ratio u _ _ growth (2^k) B room live bus venue shelves oldPos oldWide cnt
    ⟨host.1,metadata.2.1.1.trans host.1,once⟩ ⟨host.2,metadata.2.1.2.1.trans host.2,le_rfl⟩
    ⟨le_rfl,metadata.2.1.2.2,le_rfl⟩ areaU
  have caps : ∀j ∈ [growth,u,2^k,(Y).venue.degree,(Y).venue.cap,(Y).resolver.nodes,(Y).resolver.operands],
      j ≤ scale_ := original_tail_rate X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
    entry other schedule depth dr (le_rfl : u≤ scale J laneR) metadata.2.2.1 metadata.2.2.2
  have top : MaterialProgram.tailFactor growth u (2^k) (Y).venue.degree (Y).venue.cap (Y).resolver.nodes (Y).resolver.operands≤ scale J rate:=
    (MaterialProgram.tailFactor_le («Q»:=scale_) (caps _ (by simp)) (caps _ (by simp)) (caps _ (by simp)) (caps _ (by simp))
      (caps _ (by simp)) (caps _ (by simp)) (caps _ (by simp))).trans (end_rate ..)
  exact priced.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ratio top))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
