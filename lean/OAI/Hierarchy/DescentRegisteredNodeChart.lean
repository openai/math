import OAI.Hierarchy.DescentRegisteredPrimitiveCheckpoint
import OAI.Hierarchy.DescentOrdinaryFullRoleCells
import OAI.Hierarchy.DescentOrdinaryRegisteredRoleBank

namespace OAI
/-! Identify the registered ordinary primitive hardware chart with the true original
old/born node book, including its independently selected pitches. -/
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


local notation "hist_" => S.firstWidth G.b p
local notation "cap_" => S.grainAt G.b p 0
local notation "actual_" => DescentLocalArchiveOrder.PaddedOrigin.primitiveLayout
  (cap:=prior) (K₀:=ports.nodes) («s»:=hist_) («Z»:=cap_) op (Y).vector.hosts (Y).paletteShape.originBits
  S.retainedNodes (Y).rasterLanes (Y).bornBook.lanes (Y).vector.lanes (Y).palette.workLanes (Y).palette.nextLanes

include before tail cut in
theorem registered_node_chart : (Y).paletteShape=actual_:=by
  have original:=donor_date_eq X G S br ticket before tail cut
  have capac : (A).cap=(date₀).cap:=congrArg DonorDate.cap original
  have degreeAt : (A).degree=(date₀).degree:=congrArg DonorDate.degree original
  change Layout.mk (Y).vector.hosts (A).degree k (date₀).cap ((2^(k+1)-1)*(2^DescentHostDegree.packExponent 20 (date₀).degree+2))
    (S.groupCount (i+1)) ports.nodes S.retainedNodes b₀ (Y).paletteShape.originBits
    (Y).rasterLanes (Y).bornBook.lanes (Y).vector.lanes (Y).palette.workLanes (Y).palette.nextLanes=
    Layout.mk (Y).vector.hosts (A).degree k (A).cap ((2^(k+1)-1)*(2^DescentHostDegree.packExponent 20 (A).degree+2))
    (S.groupCount (i+1)) ports.nodes S.retainedNodes b₀ (Y).paletteShape.originBits
    (Y).rasterLanes (Y).bornBook.lanes (Y).vector.lanes (Y).palette.workLanes (Y).palette.nextLanes
  rw [capac,degreeAt]

include before tail cut in
theorem registered_role_axes :
    let out:=DatePorts.ordinary Y stageFloor
    (Y).vector.hosts*((2^(k+1)-1)*(2^DescentHostDegree.packExponent 20 (A).degree+2))=out.operandHosts ∧
      S.retainedNodes=out.nodes ∧ (Y).palette.nextLanes=out.roleLanes:=by
  intro out
  have slots : (Y).paletteShape.lows=(actual_).lows:=congrArg Layout.lows
    (registered_node_chart X G S br ticket before tail cut op frozen drift degree payload seats hostLanes ports old ordinary stageFloor)
  exact ⟨congrArg ((Y).vector.hosts*·) slots.symm,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
