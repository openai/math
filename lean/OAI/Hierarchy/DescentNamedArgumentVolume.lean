import OAI.Hierarchy.DescentOrdinaryArgumentDateVolume
import OAI.Hierarchy.DescentNamedFundedBaseWidth
import OAI.Hierarchy.DescentArgumentGeometryReceipt
import OAI.Hierarchy.DescentNamedSignedDate

namespace OAI
/-! # The complete native argument rectangle on a physically attained ordinary cut -/
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




def selectedArgumentRate (t f g reset driftR clipR : ℕ) :=
  20+44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose+clipR

include before tail cut in
theorem named_argument_numerics {t reset τ β copies driftR degreeMax clipR : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤ degreeMax) (pRoom : p≤ payload) (original : S.firstWidth G.b p≤ payload)
    (oldNodes : ports.nodes≤ S.retainedNodes) (oldSlots : ports.argumentsPerNode≤ S.retainedArgumentsAt G drift)
    (oldBits : ports.operandBits=DescentOperandWidth.recordBits G S k frozen drift degree p)
    (positive : 0<S.hostSize i) (ratio : ℕ)
    (clip : ((v).fundedClip ext).factor≤ scale (Nat.log 2 payload/(2*β)) clipR) :
    let J:=Nat.log 2 payload/(2*β)
    let a:=selectedArgumentRate G t f g reset driftR clipR
    (v).argumentDateCharge ports stageFloor ratio J (4*a) a≤ scale J (600*a)*ratio*((Y).rowVolume payload) ∧
    (∀j,(v).mouthParameters j≤ scale J a) ∧
    (∀j,(Y).ticketReadGeometry.coefficientInputs 32 (2^(v).area.k*(v).fundedWorkingUnit ext) j≤ scale J (4*a)) ∧
    (v).fundedMaxUnit ext≤ scale J (44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose) :=by
  intro J a
  let base:=(NativePitch.FundedBase.public_rate G t f g reset).choose
  let localR:=argumentDigitRate G t f g reset driftR base
  let U:=scale J a
  have smaller {b : ℕ} (good : b≤ a) : scale J b≤ U:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ good)
  have large : 16384≤ U:=by
    have count : 16384 ≤ scale J 14 := by
      change (2:ℕ)^14 ≤ 2^(14*(J+1))
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 14 (Nat.succ_pos J))
    exact count.trans (smaller (by dsimp only [a,selectedArgumentRate];omega))
  have measured : S=stageNumbers G t J f g reset copies (TerminalScale.tail τ J):=schedule.trans (by rw [tailBits])
  have layout : k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  have charts:=grant.book copies i p degree seats ports
  dsimp only at charts
  rw [←measured,←layout,←tailBits] at charts
  have local_bound : localR≤ a:=by dsimp only [a,localR,base,selectedArgumentRate];omega
  have sizes (j : _) : (books).bookMouthParameters j≤ U:=
    ((charts pRoom degreeRoom oldNodes oldSlots dr) j).trans (smaller (by
      apply le_trans _ local_bound
      dsimp only [localR,argumentDigitRate];omega))
  have initial:=registered_base_width X G S br ticket before tail cut op frozen drift degree payload seats
    hostLanes ports old ordinary grant schedule depth pRoom
  have chosen:=registered_width_at X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary stageFloor grant schedule depth tailBits dr initial degreeRoom pRoom original oldNodes oldSlots oldBits
  have funds : (v).fundedMaxUnit ext≤ U:=chosen.trans (smaller (by dsimp only [a,selectedArgumentRate];omega))
  have raw:=dated_material_digit X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary schedule depth
  have digit : (v).material.fieldBits≤ U:=raw.trans (smaller (by
    apply le_trans _ local_bound
    dsimp only [localR,argumentDigitRate];omega))
  have oldId:=donor_date_eq X G S br ticket before tail cut
  have sourceD:=congrArg DonorDate.degree oldId
  have sourceC:=congrArg DonorDate.cap oldId
  have site:=ports.registered_section_population ticket op g frozen p f drift degree payload seats hostLanes
    old ordinary stageFloor schedule positive radix
  have native:=ticket.selected_signed_rates schedule depth (hostRows (S.hostSize i))
    (NativePitch.incomingHosts S (i+1)) (S.groupCount (i+1)) payload
  have signed : (Y).signedLayout.unit≤ U:=native.1.trans (smaller (by
    apply le_trans _ local_bound
    dsimp only [localR,argumentDigitRate];omega))
  have fmt : (Y).signed=(Y).signedLayout.format payload:=(signed_at X G S br ticket before tail cut payload).symm
  have ms : ∀j,(v).mouthParameters j ≤ U := by
    intro j
    fin_cases j
    · exact sizes 0
    · exact (Nat.add_le_add_right sourceD.le 1).trans (sizes 1)
    · exact sizes 2
    · exact sizes 3
    · exact sizes 4
    · exact sizes 5
    · exact sizes 6
    · exact sizes 7
    · exact sizes 8
    · exact sizes 9
    · exact sizes 10
  have coeff := OrdinaryBooks.registered_selector_inputs ticket g frozen p f payload seats hostLanes old ordinary
    op drift degree ports stageFloor U (by omega) sizes sourceD.le sourceC.le digit funds
  refine ⟨?_,ms,?_,chosen⟩
  · exact OrdinaryBooks.argument_date_volume ticket g frozen p f payload seats hostLanes old ordinary op drift degree
      ports stageFloor J a ratio large sizes sourceD.le sourceC.le site radix.symm fmt digit funds signed
      (clip.trans (smaller (by dsimp only [a,selectedArgumentRate];omega)))
  · have four : U^4 = scale J (4*a) := by
      dsimp only [U,scale]
      rw [← pow_mul]
      congr 1
      ring
    exact fun j => (coeff j).trans_eq four

include before tail cut in
theorem named_argument_volume {t reset τ β copies driftR degreeMax clipR : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤ degreeMax) (pRoom : p≤ payload) (original : S.firstWidth G.b p≤ payload)
    (oldNodes : ports.nodes≤ S.retainedNodes) (oldSlots : ports.argumentsPerNode≤ S.retainedArgumentsAt G drift)
    (oldBits : ports.operandBits=DescentOperandWidth.recordBits G S k frozen drift degree p)
    (positive : 0<S.hostSize i) (ratio : ℕ)
    (clip : ((v).fundedClip ext).factor≤ scale (Nat.log 2 payload/(2*β)) clipR) :
    let J:=Nat.log 2 payload/(2*β)
    let a:=selectedArgumentRate G t f g reset driftR clipR
    (v).argumentDateCharge ports stageFloor ratio J (4*a) a≤ scale J (600*a)*ratio*((Y).rowVolume payload) :=
  (named_argument_numerics X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary stageFloor grant schedule depth tailBits dr degreeRoom pRoom original oldNodes oldSlots oldBits positive ratio clip).1

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
