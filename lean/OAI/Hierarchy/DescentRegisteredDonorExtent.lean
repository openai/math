import OAI.Hierarchy.DescentNamedOrdinaryMachine
import OAI.Hierarchy.DescentOrdinaryMountedInlet
import OAI.Hierarchy.DescentIssuedSignedChart

namespace OAI
/-! The actual packed donor register fits its allocated incoming panel at each ordinary date. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {hu : 0 ≤ (((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ))*((S.epochPower^S.priceExponent):ℝ))} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=(GroupStage.depthBound (atRound S.rounds) n f g)) (t:=S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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

include before tail cut in
theorem registered_donor_extent :
    (entry).venue.panel.base+(entry).venue.panel.size ≤ (v).donorEnd floor₁ ∧
    Overlap.rows (entry).clip.venue.hosts (entry).clip.venue.groups (entry).clip.panelPitch ≤
      (entry).venue.panel.size := by
  let date := ticket.donorDate
  let out := date.outputPorts payload seats ports.io floor₁ bits₁
  have booked := issued_return_fields X G S br ticket before tail cut books frozen payload seats
    ports.venue.lanes ports.io.roster ordinary
  have area : (base).area = date.schedule payload seats bits₁ := by
    change ticket.ordinaryArea level₁ bits₁ payload (base).unit prof seats = _
    rw [booked.2.1]; rfl
  have panel : (entry).venue.panel = out.packedDonors := rfl
  have roof : (v).donorEnd floor₁ = out.firstFree := by
    change ticket.wholeDonorEnd (base).short prof (2^level₁) payload
      ((base).area.rotationEnd ports.io.roster floor₁) = out.firstFree
    rw [booked.1, area]; rfl
  have pitch : (entry).clip.panelPitch = lanes payload date.amount := by
    change lanes payload (ticket.installedDonorWidth (base).short prof) = _
    rw [booked.1]; rfl
  have fit := date.output_room payload seats ports.io floor₁ bits₁
  have last : out.packedDonors.base+out.packedDonors.size = out.meter := fit.2.2.2.2.1
  have meter : out.meter+1+date.hosts*chunks date.groups (lanes payload date.amount) < out.firstFree :=
    fit.2.2.2.2.2
  rw [panel, roof, last, pitch]
  refine ⟨by omega, ?_⟩
  change date.hosts*chunks date.groups (lanes payload date.amount) ≤
    2^Nat.clog 2 (date.hosts*chunks date.groups (lanes payload date.amount))
  exact Nat.le_pow_clog (by decide) _

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
