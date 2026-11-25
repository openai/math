import OAI.Hierarchy.DescentPaidRegisteredInput
import OAI.Hierarchy.DescentNamedFundedBaseWidth
import OAI.Hierarchy.DescentChosenGrainRoom
import OAI.Hierarchy.DescentDatePortArchivePitchRoom

namespace OAI
/-! # Registered date bills at the selected public socket width -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
theorem ArchivePitchRoom.inputPitch {port : DatePorts} {groups h a b : ℕ}
    (room : port.ArchivePitchRoom groups h a b) (axes : port.venue.groups=groups) :
    InputPitch port h (max a b) :=by
  have filed:=room.toArchiveDensity.weaken (le_max_left a b) (le_max_right a b)
  rw [←axes] at filed
  exact ⟨⟨room.operandPos,room.operandHalf.trans (Nat.div_le_self ..)⟩,
    ⟨room.rolePos,room.roleHalf.trans (Nat.div_le_self ..)⟩,filed.operands,filed.roles⟩
end Hierarchy.DescentSixParty.Chronology.DatePorts

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





variable {t reset τ β copies driftR degreeMax ratio : ℕ}
local notation "J₀" => Nat.log 2 payload/(2*β)
local notation "startRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "funds₀" => 44*argumentDigitRate G t f g reset driftR startRate
local notation "laneR" => returnLaneRate G t f g reset funds₀
local notation "inputs" => (v).registeredEntry ports stageFloor
variable (actual : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (resources : ReturnCalendar G t f g reset driftR (44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose) τ β ratio payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β))) (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (degreeRoom : degree≤degreeMax) (bin sockets : ℕ) (openSocket : 0<sockets)
    (split : p=bin*(payload/(16*((sockets*(G.b^(S.rounds*S.height)*G.b))*bin))))
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (pPos : 0<p)

include before tail cut actual resources schedule depth tailBits dr degreeRoom openSocket split archive slots pPos in
theorem chosen_registered_resources :
    (v).fundedMaxUnit ext ≤ scale J₀ funds₀ ∧
    (0<(Y).resolver.lanes ∧ (Y).resolver.lanes≤payload/2 ∧ payload≤(Y).resolver.lanes*scale J₀ laneR) ∧
    (∀ prevArg prevRole (_population : DatePorts.Population S ports i),
      ports.ArchivePitchRoom (S.groupCount i) payload (scale J₀ prevArg) (scale J₀ prevRole) →
      ∀floor w,0<S.hostSize i→w≤ratio*payload→
      (Y).inputFee inputs floor w ≤ ratio*scale J₀ (inputReadRate G t f g reset driftR startRate (max prevArg prevRole))*
        MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload) ∧
    (2^payload≤2*copies → 0<S.hostSize i →
      (∀j<S.length,j%(S.rounds+1)≠S.rounds→
        (ordinary j).payload=payload ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount) →
      ∀floor w (source : StageVenueTail.Sources) (room : (Y).ResultRoom floor source w),
      w≤ratio*payload →
      let K₀:=ratio*scale J₀ (returnDateRate G t f g reset driftR funds₀)
      (Y).tailAmount floor w source room≤S.hostSize i*payload*(K₀+1)+
        S.hostSize i*(S.groupCount i*S.radix)*K₀) :=by
  have seedWidth : S.firstWidth G.b p≤payload:=by
    rw [split];exact S.split_first_width G.b payload bin sockets openSocket
  have grain:=S.grain_le_payload G.b p payload G.base_pos seedWidth
  have basePrice:=registered_base_width X G S br ticket before tail cut op frozen drift degree payload seats
    hostLanes ports old ordinary actual schedule depth grain
  have combined:=registered_width_at X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual schedule depth tailBits dr basePrice degreeRoom grain seedWidth
    (DatePorts.ArchiveWidths.node_bound G S op archive) slots archive.digits
  have lanes:=registered_row_room X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual resources schedule depth tailBits dr basePrice degreeRoom grain seedWidth archive slots pPos
  refine ⟨combined,lanes,?_,?_⟩
  · intro prevArg prevRole _population source floor w live bus
    have p₀:=source.inputPitch _population.groups
    have mono {j m : ℕ} (z : j≤ m) : scale J₀ j ≤ scale J₀ m:=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ z)
    have same : max (scale J₀ prevArg) (scale J₀ prevRole)=scale J₀ (max prevArg prevRole):=by
      rcases le_total prevArg prevRole with h|h
      · rw [max_eq_right h,max_eq_right (mono h)]
      · rw [max_eq_left h,max_eq_left (mono h)]
    rw [same] at p₀
    exact paid_registered_inputs X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
      old ordinary stageFloor actual resources schedule depth tailBits dr basePrice degreeRoom grain seedWidth archive slots
      pPos _population p₀ floor w live bus
  · exact named_registered_paid X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
      old ordinary stageFloor actual resources schedule depth tailBits dr basePrice degreeRoom grain seedWidth archive slots pPos

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
