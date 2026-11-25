import OAI.Hierarchy.DescentRegisteredPrimitiveFunding
import OAI.Hierarchy.DescentRegisteredPrimitiveRooms

namespace OAI
/-! Available addresses and the issuing stage's complete rectangular read capacities. -/
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


include radix in
theorem registered_primitive_rooms (age : i<S.length) (arity : ports.argumentsPerNode≤(v).vector.operands)
    {w unit : ℕ} (earlier : (Y₀).Room Y stageFloor w) (budget : (L₀).Funding payload unit)
    (finalPage : (Y).primitiveRoof ((Y).operandEnd stageFloor)<2^w) :
    (Y).PrimitiveRoom stageFloor Y₀ w ∧
      (L₀).Capacity ((Y).primitiveSources stageFloor Y₀ ((v).registered_match ports stageFloor arity) rfl):=by
  have order:=(v).registered_primitive_input_order stageFloor ports arity
  have groups : S.groupCount i=S.groupCount (i+1)*2^k:=by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr (S.groupDigits age radix)
  exact (Y).primitive_input_rooms stageFloor Y₀ ((v).registered_match ports stageFloor arity) rfl earlier budget
    order.1 order.2 finalPage rfl groups rfl rfl groups

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
