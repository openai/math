import OAI.Hierarchy.DescentNamedMaterialDigit
import OAI.Hierarchy.DescentRegisteredWidthCalendar
import OAI.Hierarchy.DescentNamedRegisteredEnd

namespace OAI
/-! # The selectors of the actual preceding row fit the registered ordinary operand purchase -/
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
theorem registered_width_at {t reset τ β copies driftR base degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits : frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR)
    (baseWidth : (v).fundedMaxUnit 0 ≤ scale (Nat.log 2 payload/(2*β)) base)
    (degreeRoom : degree≤degreeMax) (pRoom : p≤payload) (original : S.firstWidth G.b p≤payload)
    (oldNodes : ports.nodes≤S.retainedNodes) (oldSlots : ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (oldBits : ports.operandBits=DescentOperandWidth.recordBits G S k frozen drift degree p) :
    (v).fundedMaxUnit ext ≤ scale (Nat.log 2 payload/(2*β)) (44*argumentDigitRate G t f g reset driftR base) :=by
  let J:=Nat.log 2 payload/(2*β)
  let r:=argumentDigitRate G t f g reset driftR base
  let U:=scale J r
  have mono {a b : ℕ} (le : a≤b) : scale J a≤ scale J b:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have toBound {a : ℕ} (le : a≤r) : scale J a≤U:=mono le
  have funds : 8192≤U:=by
    have count : 8192 ≤ scale J 13 := by
      change (2:ℕ)^13 ≤ 2^(13*(J+1))
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 13 (Nat.succ_pos J))
    exact count.trans (toBound (by dsimp only [r,argumentDigitRate];omega))
  have small3:=toBound (a:=3) (by dsimp only [r,argumentDigitRate];omega)
  have measured : S=stageNumbers G t J f g reset copies (TerminalScale.tail τ J):=schedule.trans (by rw [tailBits])
  have layout : k=groupBits t J S.hostGain S.capGain (cutRate t f g):=by rw [schedule];exact depth
  have chart:=grant.book copies i p degree seats ports
  dsimp only at chart
  rw [←measured,←layout,←tailBits] at chart
  have span:=chart pRoom degreeRoom oldNodes oldSlots dr
  have tab (j : _) : (books).bookMouthParameters j≤U:=(span j).trans (toBound (by dsimp only [r,argumentDigitRate];omega))
  have ids:=donor_date_eq X G S br ticket before tail cut
  have degreeId:=congrArg DonorDate.degree ids
  have capId:=congrArg DonorDate.cap ids
  have archived:=grant.archive copies p degree
  dsimp only at archived
  rw [←measured,←depth,←tailBits] at archived
  have prev : ports.operandBits≤U:=oldBits ▸ (archived pRoom degreeRoom).trans small3
  have prints:=(grant.printed (S.firstWidth G.b p) (S.grainAt G.b p 0)
    (Nat.le_mul_of_pos_right _ G.base_pos) original).trans small3
  have digit:=dated_material_digit X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports
    old ordinary schedule depth
  have reader:=grant.census copies frozen p i g pRoom
  dsimp only at reader
  rw [←schedule,←depth] at reader
  have money:=(NativePitch.all_donor_rate G t f g reset).choose_spec J copies frozen p i
  dsimp only at money
  rw [←schedule,←layout] at money
  have full:=OrdinaryBooks.registered_argument_unit ticket g frozen p f payload seats hostLanes old ordinary
    op drift degree ports stageFloor U funds tab degreeId.le capId.le prev prints
    (digit.trans (toBound (by dsimp only [r,argumentDigitRate];omega)))
    ((reader.trans money.2).trans (toBound (by dsimp only [r,argumentDigitRate];omega)))
    (baseWidth.trans (toBound (by dsimp only [r,argumentDigitRate];omega)))
  apply full.trans_eq
  change (2^(r*(J+1)))^44=2^((44*r)*(J+1))
  rw [←pow_mul];congr 1;ring

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
