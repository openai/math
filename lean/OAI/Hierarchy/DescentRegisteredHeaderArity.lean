import OAI.Hierarchy.DescentPrefixArgumentCapacity
import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentOrdinaryRegisteredHeaderRoom
import OAI.Hierarchy.DescentArchivePointerRows

namespace OAI
/-! Numerical room for the writer at the true source and successor archives of an ordinary cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
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
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "floor₁" => (v).stageStart root
local notation "level₁" => Nat.clog 2 (S.hostSize i)
local notation "bits₁" => S.censusBits p
local notation "prof" => DescentTerminalEpochBits.width G.C


local notation "rotation" => ((d₀).schedule payload seats bits₁).rotationEnd ports.io.roster floor₁

open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentRetainedRangeDigits
local notation "nextPath" => before.ordinary ticket
variable (positive:0<p) (height:0<S.height) (bound:G.b≤2^S.capGain)
    (limit:R≤drift) (hw:(before.ordinary ticket).whole p)
local notation "archive" => (nextPath).archive p positive br.origin.archive hw
variable (sh:WorldShape p R ((before.ordinary ticket).archive p positive br.origin.archive hw).bit)

include height bound limit in
theorem header_recipe_room (site:norm.result.graph.Site) (node:((archive).bit.recipe site).Node) :
    ((sh.sites site).recipe positive).arity node≤(v).resolver.operands :=by
  rw [←DescentRetainedRangeDigits.length (sh.sites site) node positive]
  have real:=Branch.prefix_argument_capacity X G S br positive nextPath hw height bound sh site node
  apply real.trans
  change S.retainedArgumentsAt G R≤ max ports.argumentsPerNode (S.retainedArgumentsAt G drift)
  exact (Nat.mul_le_mul_right _ (Nat.add_le_add_right limit 1)).trans (Nat.le_max_right ..)

include height bound limit in
theorem header_recipe_word (previous:ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (site:norm.result.graph.Site) (node:((archive).bit.recipe site).Node) :
    ((sh.sites site).recipe positive).arity node<2^(v).finalChart.field :=
  (header_recipe_room X G S br ticket before op frozen drift degree payload seats root ports ordinary
    positive height bound limit hw sh site node).trans_lt
    (DatePorts.ordinary_header_arity_width ports ticket op g frozen p f drift degree payload seats root ordinary previous)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
