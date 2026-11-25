import OAI.Hierarchy.DescentNamedRegisteredWidth
import OAI.Hierarchy.DescentDateArgumentSlots

namespace OAI
/-! # The actual successor operand pitch and its complete calibrated end-of-date charge -/
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
include before tail cut actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive slots pPos in
theorem registered_row_funding :
    (Y).FundedCaps payload (4*(v).area.unit) ((v).fundedWorkingUnit ext)
      ((2^k)*(v).fundedWorkingUnit ext) ∧
    (2^k)*(v).fundedWorkingUnit ext ≤ scale J₀ laneR :=by
  have bought:=registered_width_at (t:=t) (reset:=reset) (τ:=τ) (β:=β) (copies:=copies) (driftR:=driftR) (base:=base) (degreeMax:=degreeMax) X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual schedule depth tailBits dr baseWidth degreeRoom pRoom original
    (DatePorts.ArchiveWidths.node_bound G S op archive) slots archive.digits
  have rb : 2^k ≤ scale J₀ (groupRate G t f g reset):=by
    rw [depth]
    exact Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have combined:=(Nat.mul_le_mul rb bought).trans_eq (scale_mul ..)
  have cap:= (tail_unit_rows («s»:=0) combined (Nat.zero_le (scale J₀ (signedRates G t f g reset).amount))
    (incomingRate G t f g reset)).1
  have density : (2^k)*(v).fundedWorkingUnit ext ≤ scale J₀ laneR:=((v).source_density ext).2.le.trans cap
  have form : 4*(v).fundedMaxUnit ext*2^k≤payload:=by
    have scaled : 4*(v).fundedMaxUnit ext*2^k ≤ scale J₀ laneR:=by
      calc
        _ = 4*((2^k)*(v).fundedMaxUnit ext):=by ring
        _ ≤ _ := (Nat.mul_le_mul_right _ (by decide : 4≤8)).trans cap
    have w:=resources.width
    omega
  have money:=resources.census copies frozen p i g pRoom
  dsimp only at money
  rw [←schedule,←depth] at money
  have paid : 0<S.censusBits p:=by
    have live:=Nat.clog_pos (by decide : 1<2) (show 1<p+1 by omega)
    unfold AtomSchedule.censusBits;omega
  have receipt:=(v).funded_argument_bounds ext entry paid money form
  exact ⟨⟨receipt.positive, receipt.clipped, receipt.out, receipt.oldCap, receipt.clipCap,
    receipt.outCap, receipt.paid, receipt.raw, receipt.table, receipt.masks, receipt.sums,
    receipt.clipBits, receipt.outBits, receipt.fill₀, receipt.fill₁, receipt.fill₂⟩, density⟩

include before tail cut actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive slots pPos in
theorem registered_row_room :
    0<(Y).resolver.lanes ∧ (Y).resolver.lanes≤payload/2 ∧ payload≤(Y).resolver.lanes*scale J₀ laneR :=by
  obtain ⟨receipt,density⟩:=registered_row_funding X G S br ticket before tail cut op frozen drift degree payload
    seats hostLanes ports old ordinary stageFloor actual resources schedule depth tailBits dr baseWidth degreeRoom
    pRoom original archive slots pPos
  have fits : (Y).resolver.lanes≤payload/2 :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos receipt.paid (Nat.two_pow_pos k))).trans receipt.outBits
  exact ⟨receipt.out,fits,receipt.fill₂.trans (Nat.mul_le_mul_left _ density)⟩

include before tail cut actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive slots pPos in
theorem named_registered_paid (large : 2^payload≤2*copies) (live : 0<S.hostSize i)
    (stored : ∀j<S.length,j%(S.rounds+1)≠S.rounds→
      (ordinary j).payload=payload ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount)
    (floor w : ℕ) (source : StageVenueTail.Sources) (room : (Y).ResultRoom floor source w) (bus : w≤ratio*payload) :
    let K₀:=ratio*scale J₀ (returnDateRate G t f g reset driftR funds₀)
    (Y).tailAmount floor w source room≤S.hostSize i*payload*(K₀+1)+S.hostSize i*(S.groupCount i*S.radix)*K₀ :=by
  have bought:=registered_width_at (t:=t) (reset:=reset) (τ:=τ) (β:=β) (copies:=copies) (driftR:=driftR) (base:=base) (degreeMax:=degreeMax) X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual schedule depth tailBits dr baseWidth degreeRoom pRoom original
    (DatePorts.ArchiveWidths.node_bound G S op archive) slots archive.digits
  exact named_registered_end X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports old
    ordinary stageFloor resources schedule depth tailBits large dr live slots bought pPos pRoom stored
    floor w source room bus

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
