import OAI.Hierarchy.DescentNamedOrdinaryExecution
import OAI.Hierarchy.DescentNamedDonorPairBudget

namespace OAI
/-! # The true installed donor's extent on the public ordinary ticket -/
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


open DescentDatedAddressBook DescentSIMDLookup DescentPackedColony DescentPackedProfileInstall
local notation "plan₀" => (d₀).schedule payload seats bits₁
local notation "match_" => (base).registered_match ports floor₁ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry ports floor₁

include before tail cut in
theorem installed_donor_roof :
    ticket.wholeDonorEnd (max (k+3) (Nat.clog 2 ((A).degree+1))) prof (hostRows (S.hostSize i)) payload rotation ≤ (v).endAddress floor₁ := by
  have actual:=donor_date_eq X G S br ticket before tail cut
  have issuedFields:=issued_return_fields X G S br ticket before tail cut books frozen payload seats ports.venue.lanes ports.io.roster ordinary
  have a:(base).area=ticket.donorDate.schedule payload seats bits₁:=by
    change ticket.ordinaryArea level₁ bits₁ payload (base).unit prof seats=_
    rw [issuedFields.2.1]; rfl
  have deposit:(v).donorEnd floor₁=ticket.wholeDonorEnd
      (max (k+3) (Nat.clog 2 ((A).degree+1))) prof (hostRows (S.hostSize i)) payload rotation:=by
    change ticket.wholeDonorEnd (base).short prof (2^level₁) payload ((base).area.rotationEnd ports.io.roster floor₁)=_
    rw [issuedFields.1,a,actual]; rfl
  have one : (v).donorEnd floor₁ ≤ (v).signedEnd floor₁:=by rw [(v).signed_extent];exact Nat.le_add_right ..
  have two : (v).signedEnd floor₁ ≤ (v).refsStart floor₁:=Nat.le_add_right ..
  obtain ⟨first,a₀⟩:=(v).mount_order floor₁
  obtain ⟨a₁,a₂,a₃,a₄,a₅⟩:=(v).routed_order floor₁
  rw [←deposit]
  omega

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
