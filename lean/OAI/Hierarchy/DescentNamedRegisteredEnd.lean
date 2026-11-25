import OAI.Hierarchy.DescentRegisteredTailFunding
import OAI.Hierarchy.DescentRegisteredTailCalendar

namespace OAI
/-! # The calibrated real ordinary suffix at its exact physical register state -/
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
local notation "u" => price*(wire:ℝ)
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
theorem named_registered_end {t reset τ β copies driftR funds ratio : ℕ}
    (grant : ReturnCalendar G t f g reset driftR funds τ β ratio payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β))) (size : 2^payload≤2*copies)
    (dr : drift+1≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (live : 0<S.hostSize i) (args : ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (maxUnit : (v).fundedMaxUnit ext≤ scale (Nat.log 2 payload/(2*β)) funds)
    (pv : 0<p) (pFits : p≤payload)
    (stored : ∀j<S.length,j%(S.rounds+1)≠S.rounds→
      (ordinary j).payload=payload ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount)
    (floor w : ℕ) (source : StageVenueTail.Sources) (room : (Y).ResultRoom floor source w) (bus : w≤ratio*payload) :
    let R:=ratio*scale (Nat.log 2 payload/(2*β)) (returnDateRate G t f g reset driftR funds)
    (Y).tailAmount floor w source room≤S.hostSize i*payload*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R :=by
  intro R
  let J:=Nat.log 2 payload/(2*β)
  have intake:=grant.census copies frozen p i g pFits
  change (stageNumbers G t J f g reset copies frozen).censusBits p≤_ at intake
  rw [←schedule,←depth] at intake
  have paid : 0<S.censusBits p:=by
    have n:=Nat.clog_pos (by decide : 1<2) (show 1<p+1 by omega)
    unfold AtomSchedule.censusBits;omega
  let calendarRows (H : ℕ) :=grant.rows copies p (i+1) H
  have C : S=stageNumbers G t J f g reset copies (TerminalScale.tail τ J):=schedule.trans (by rw [tailBits])
  have key : k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  have next (H : ℕ) : 0<Z ∧ Z≤payload/2 ∧ H*DescentSIMDLookup.chunks (S.groupCount (i+1)) Z*payload≤
      H*payload+H*S.groupCount (i+1)*scale J (incomingRate G t f g reset):=by
    have h₀:=calendarRows H
    dsimp only at h₀
    rw [←C,←key,←tailBits] at h₀
    exact h₀ ordinary pFits stored
  have z:=next 0
  have bill:=registered_tail_invoice X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor schedule depth dr live args maxUnit paid intake
    ⟨z.1,z.2.1,fun H=>(next H).2.2⟩ floor w ratio source room bus grant.width
  have top:=grant.paid J copies frozen i ((Y).tailAmount floor w source room) (Nat.div_le_self ..) size
  rw [←schedule] at top
  exact top bill

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
