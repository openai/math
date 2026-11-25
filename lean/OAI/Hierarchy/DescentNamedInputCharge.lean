import OAI.Hierarchy.DescentPhysicalInputFee
import OAI.Hierarchy.DescentNamedRegisteredSuffix
import OAI.Hierarchy.DescentDatePopulation
import OAI.Hierarchy.DescentRetainedMovementBits

namespace OAI
/-! # The two true argument-entry input fees on the original selected calendar -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentSIMDLookup
structure InputPitch (ports : DatePorts) (h U : ℕ) : Prop where
  old : 0<ports.operandLanes ∧ ports.operandLanes≤h
  role : 0<ports.roleLanes ∧ ports.roleLanes≤h
  operands : ports.venue.groups≤ports.operandLanes ∨ h≤ports.operandLanes*U
  roles : ports.venue.groups≤ports.roleLanes ∨ h≤ports.roleLanes*U
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




variable {t reset τ β copies driftR base degreeMax ratio : ℕ}
local notation "J₀" => Nat.log 2 payload/(2*β)
local notation "funds₀" => 44*argumentDigitRate G t f g reset driftR base
local notation "laneR" => returnLaneRate G t f g reset funds₀
variable (actual : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (resources : ReturnCalendar G t f g reset driftR (44*argumentDigitRate G t f g reset driftR base) τ β ratio payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (baseWidth : ((OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports).onTicket ticket g frozen p f payload seats hostLanes old ordinary).fundedMaxUnit 0 ≤ scale (Nat.log 2 payload/(2*β)) base)
    (degreeRoom : degree≤degreeMax) (pRoom : p≤payload) (original : S.firstWidth G.b p≤payload)
    (archive : DatePorts.ArchiveWidths G S op ports k frozen p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (pPos : 0<p)

local notation "inputs" => (v).registeredEntry ports stageFloor
include before tail cut actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive slots pPos in
theorem registered_input_charge {paidRows : ℕ} (pop : DatePorts.Population S ports i)
    (priorPitch : DatePorts.InputPitch ports payload paidRows)
    (floor w : ℕ) (live : 0<S.hostSize i) (bus : w≤ratio*payload) :
    let U:=max paidRows (scale J₀ laneR)
    let count:=7*ports.argumentsPerNode*2^k
    (Y).inputFee inputs floor w ≤ ratio*(MaterialProgram.retileFactor count U+
      MaterialProgram.retileFactor (2^k) U)*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload :=by
  intro U count
  let clip:=(v).fundedClip ext
  have real:=registered_row_room X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive slots pPos
  have pos : 0<clip.postPitch:=real.1
  have grow : clip.postPitch≤clip.working:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
  have workPos : 0<clip.working:=pos.trans_le grow
  have fill : payload≤clip.working*U:=real.2.2.trans (Nat.mul_le_mul grow (le_max_right ..))
  have workCap : clip.working≤payload:=by
    change clip.postPitch*clip.radix≤payload
    apply (Nat.mul_le_mul_right _ ((Nat.min_le_left ..) : clip.postPitch≤clip.panelPitch/clip.radix)).trans
    apply (Nat.div_mul_le_self ..).trans
    change lanes payload _≤payload
    exact Nat.div_le_self ..
  let H:=ports.operandHosts
  have srcWide : 2≤ports.operandBits:=by
    rw [archive.digits,←(OrdinaryBooks.record_width G S op g k i p frozen drift degree payload seats ports).1]
    omega
  have equal : (inputs).previous.groups=(inputs).clip.venue.groups:=pop.groups
  have capOld : H≤2*S.hostSize i:=pop.earlier.trans (pop.venue_high.trans (hostRows_double live))
  have capNew : (inputs).clip.venue.hosts≤2*S.hostSize i:=hostRows_double live
  have operandWidth : DescentOrdinaryPriorRetile.digits (inputs).previous*(inputs).previous.lanes≤payload/2:=by
    change ((ports.operandBits-2+2)*ports.nodes)*ports.operandLanes≤_
    simpa only [Nat.sub_add_cancel srcWide] using archive.operands
  have oldreel:=DescentResetRetainedSetup.Layout.bounded_pitch_rows (H:=H) priorPitch.old.1 priorPitch.operands
  have reel:=DescentResetRetainedSetup.Layout.bounded_pitch_rows (H:=H) priorPitch.role.1 priorPitch.roles
  have cash : paidRows≤U:=le_max_left ..
  have up {x : ℕ} (z : x≤H*payload+H*ports.venue.groups*paidRows) : x≤H*payload+H*ports.venue.groups*U:=
    z.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ cash) _)
  have first:=up oldreel
  have second:=up reel
  rw [pop.groups] at second
  exact (Y).input_charge inputs floor w (S.hostSize i) payload ratio U live equal ⟨pop.positive,capOld⟩ capNew
    ⟨operandWidth,archive.roles⟩ ⟨priorPitch.old.1,priorPitch.old.2,priorPitch.role.1,priorPitch.role.2⟩
    ⟨first,second⟩ ⟨workPos,workCap,fill⟩ bus

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
