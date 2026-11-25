import OAI.Hierarchy.DescentNamedInputCharge
import OAI.Hierarchy.DescentInputWordRate

namespace OAI
/-! # Funded real prior-pad and printed-role phases of the registered 12-step operand entry -/
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
theorem paid_registered_inputs {prev : ℕ} (population : DatePorts.Population S ports i)
    (source : DatePorts.InputPitch ports payload (scale J₀ prev))
    (floor w : ℕ) (live : 0<S.hostSize i) (bus : w≤ratio*payload) :
    (Y).inputFee inputs floor w ≤ ratio*scale J₀ (inputReadRate G t f g reset driftR base prev)*
      MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload :=by
  have bill:=registered_input_charge X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary stageFloor actual resources schedule depth tailBits dr baseWidth degreeRoom pRoom original archive
    slots pPos population source floor w live bus
  let a:=driftR+operandExponent G (stageNumbers G t 0 f g reset 0 0)
  let r:=groupRate G t f g reset
  let q:=3+a+r
  have epoch : S.height=J₀:=by rw [schedule];rfl
  have gr:=S.capacities_at_scale G drift driftR (epoch.symm ▸ dr)
  have ar : ports.argumentsPerNode ≤ scale J₀ a:=by
    have slotLimit:=slots.trans gr.2
    simpa only [a, schedule, stageNumbers, operandExponent, AtomSchedule.localGrainExponent] using slotLimit
  have rad : 2^k ≤ scale J₀ r:=by rw [depth];exact Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have mono {n m : ℕ} (increase : n≤ m) : scale J₀ n ≤ scale J₀ m:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ increase)
  have seven : 7 ≤ scale J₀ 3:=(by decide : 7≤2^3).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 3 (Nat.succ_pos J₀)))
  have amount : 7*ports.argumentsPerNode*2^k ≤ scale J₀ q :=
    (Nat.mul_le_mul ((Nat.mul_le_mul seven ar).trans_eq (scale_mul J₀ 3 a)) rad).trans_eq (scale_mul ..)
  have older:=mono (show prev≤prev+laneR by omega)
  have newer:=mono (show laneR≤prev+laneR by omega)
  have factorBound:=input_factors newer amount (rad.trans (mono (show r≤q by dsimp [q];omega))) older
  have paid : MaterialProgram.retileFactor (7*ports.argumentsPerNode*2^k) (max (scale J₀ prev) (scale J₀ laneR))+
      MaterialProgram.retileFactor (2^k) (max (scale J₀ prev) (scale J₀ laneR)) ≤ scale J₀ (inputReadRate G t f g reset driftR base prev) :=by
    simpa only [inputReadRate,q,a,r,Nat.add_assoc] using factorBound
  exact bill.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ratio paid))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
