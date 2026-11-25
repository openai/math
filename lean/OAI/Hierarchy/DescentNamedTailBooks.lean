import OAI.Hierarchy.DescentOrdinaryBooksAtDate
import OAI.Hierarchy.DescentNamedTailFunding
import OAI.Hierarchy.DescentOrdinaryHostShelfRoom

namespace OAI
/-! # Genuine resolver dimensions for the named ordinary calendar's numeric book constructor -/
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
variable (entry : PhysicalOrdinary.ArgumentEntry
  ((OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports).onTicket
    ticket g frozen p f payload seats hostLanes old ordinary)) (other : ℕ)
local notation "ext" => max ((v).fullArgumentUnit entry) other
local notation "Y" => (v).withFundedArguments ext entry

include before tail cut in
theorem registered_tail_books {t J reset M last : ℕ} (schedule : S=stageNumbers G t J f g reset M last)
    (live : 0<S.hostSize i) (args : ports.argumentsPerNode≤S.retainedArgumentsAt G drift) :
    (Y).resolver.lanes=((v).fundedClip ext).postPitch ∧
    ((Y).resolver.hosts≤NativePitch.incomingHosts S (i+1) ∧
      (Y).resolver.groups≤S.groupCount (i+1) ∧ (Y).resolver.blocks≤2^k) ∧
    (Y).resolver.nodes≤S.retainedNodes ∧ (Y).resolver.operands≤S.retainedArgumentsAt G drift :=by
  have chart:=donor_date_eq X G S br ticket before tail cut
  have d : (A).degree=(DonorDate.atDate G S g k i p).degree:=congrArg DonorDate.degree chart
  obtain ⟨j,hj,slot⟩:=ticket.degreeSlot
  have stage : j<t:=by simpa only [schedule,stageNumbers] using hj
  have seat := OrdinaryBooks.round_slots reset stage
  have gain : 4*DescentOrdinaryVenueReturn.shapeSlots (DonorDate.atDate G S g k i p).degree≤2^S.hostGain:=by
    rw [←d,prior.branch,slot]
    simpa only [schedule,stageNumbers] using seat
  have real:=OrdinaryBooks.compact_host_room S live ticket.hubRows.choose radix gain
  refine ⟨rfl,⟨real,le_rfl,le_rfl⟩,le_rfl,?_⟩
  exact max_le args le_rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
