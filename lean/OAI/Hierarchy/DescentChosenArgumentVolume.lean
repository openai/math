import OAI.Hierarchy.DescentNamedArgumentVolume
import OAI.Hierarchy.DescentIngressFactorPolynomial

namespace OAI
/-! # All public scalar rates of the chosen ordinary argument phase -/
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





open DescentOrdinaryVenueIngress

def chosenClipRate (t f g reset driftR : ℕ) :=20*(14+argumentMouthRate G t f g reset driftR)
include before tail cut in
theorem chosen_argument_numerics {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤ degreeMax) (pRoom : p≤ payload) (original : S.firstWidth G.b p≤ payload)
    (oldNodes : ports.nodes≤ S.retainedNodes) (oldSlots : ports.argumentsPerNode≤ S.retainedArgumentsAt G drift)
    (oldBits : ports.operandBits=DescentOperandWidth.recordBits G S k frozen drift degree p)
    (positive : 0<S.hostSize i) (ratio : ℕ)
 :
    let J:=Nat.log 2 payload/(2*β)
    let a:=selectedArgumentRate G t f g reset driftR (chosenClipRate G t f g reset driftR)
    (v).argumentDateCharge ports stageFloor ratio J (4*a) a ≤ scale J (600*a)*ratio*((Y).rowVolume payload) ∧
    (∀j,(v).mouthParameters j≤ scale J a) ∧
    (∀j,(Y).ticketReadGeometry.coefficientInputs 32 (2^(v).area.k*(v).fundedWorkingUnit ext) j≤ scale J (4*a)) ∧
    (v).fundedMaxUnit ext≤ scale J (44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose) :=by
  let J:=Nat.log 2 payload/(2*β)
  let a:=14+argumentMouthRate G t f g reset driftR
  let U:=scale J a
  have large : 16384 ≤ U:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (show 14≤a*(J+1) by dsimp [a];nlinarith)
  have measured : S=stageNumbers G t J f g reset copies (TerminalScale.tail τ J):=schedule.trans (by rw [tailBits])
  have layout : k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  have charts:=grant.book copies i p degree seats ports
  dsimp only at charts
  rw [←measured,←layout,←tailBits] at charts
  have sizes (j : Fin 11) : (books).bookMouthParameters j ≤ U:=
    ((charts pRoom degreeRoom oldNodes oldSlots dr) j).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (show argumentMouthRate G t f g reset driftR ≤ a by dsimp [a];omega)))
  have eqd:=donor_date_eq X G S br ticket before tail cut
  have sd : prior.placement.degree=(books).reference.degree:=congrArg DonorDate.degree eqd
  have sc : prior.placement.cap=(books).reference.capacity:=congrArg DonorDate.cap eqd
  have degree₀ : prior.placement.degree ≤ U:=by
    rw [sd];exact (Nat.le_succ _).trans (sizes 1)
  have cap₀ : prior.placement.cap ≤ U:=by rw [sc];exact sizes 4
  have blocks : 2^k ≤ U:=sizes 2
  have factor : ((v).fundedClip ext).factor ≤ scale J (chosenClipRate G t f g reset driftR):=by
    change ingressFactor prior.placement.degree (2^k) prior.placement.cap ≤ _
    calc
      _ ≤ U^20:=ingressFactor_le _ _ _ _ large degree₀ blocks cap₀
      _ = _:=by dsimp [U,a,scale,chosenClipRate];rw [←pow_mul];congr 1;ring
  exact named_argument_numerics X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor grant schedule depth tailBits dr degreeRoom pRoom original oldNodes oldSlots oldBits
    positive ratio factor

include before tail cut in
theorem chosen_argument_volume {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤ degreeMax) (pRoom : p≤ payload) (original : S.firstWidth G.b p≤ payload)
    (oldNodes : ports.nodes≤ S.retainedNodes) (oldSlots : ports.argumentsPerNode≤ S.retainedArgumentsAt G drift)
    (oldBits : ports.operandBits=DescentOperandWidth.recordBits G S k frozen drift degree p)
    (positive : 0<S.hostSize i) (ratio : ℕ)
 :
    let J:=Nat.log 2 payload/(2*β)
    let a:=selectedArgumentRate G t f g reset driftR (chosenClipRate G t f g reset driftR)
    (v).argumentDateCharge ports stageFloor ratio J (4*a) a ≤ scale J (600*a)*ratio*((Y).rowVolume payload) :=
  (chosen_argument_numerics X G S br ticket before tail cut op frozen drift degree payload seats hostLanes
    ports old ordinary stageFloor grant schedule depth tailBits dr degreeRoom pRoom original oldNodes oldSlots oldBits positive ratio).1

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
