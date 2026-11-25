import OAI.Hierarchy.DescentNamedRegisteredPrograms
import OAI.Hierarchy.DescentRegisteredReturnPorts

namespace OAI
/-! # The outgoing public date registers of the actual ordinary cut -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentOrdinaryVenueIngress StageVenueTail
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
set_option quotPrecheck false
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
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

local notation "floor" => (v).stageStart root
local notation "entry" => (base).registeredEntry ports start
local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "rawDate" => Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes

local notation "clip₀" => OrdinaryBooks.purchaseClip G books core ports (rawDate).paidBits
local notation "selectedBooks" => OrdinaryBooks.purchased G books core ports (rawDate).paidBits


include before tail cut in
theorem ordinaryPorts_public (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area):
    let published:=registered_program_paths X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary paths
    let assigned:VenueProgram.Registered:=
      ⟨core,selectedBooks,{rawDate with paidLanes:=(clip₀).postPitch,aliveLanes:=(clip₀).postPitch},clip₀,published⟩
    DatePorts.ordinaryPorts ports ticket op g frozen p f drift degree payload seats root ordinary=assigned.next G ∧
      (v).countAddr root=assigned.selector G ∧ (v).fullEnd root=assigned.roof G:=by
  intro published assigned
  obtain ⟨theBooks,theClip⟩:=registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have eq:=registered_return_inputs X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary selectedBooks clip₀ theBooks theClip paths published
  obtain ⟨headers,select,roof⟩:=(v).registered_return_ports root entry paths rfl
  exact ⟨headers.trans (congrArg (fun b:VenueProgram.Registered=>b.next G) eq),
    select.trans (congrArg (fun b:VenueProgram.Registered=>b.selector G) eq),
    roof.trans (congrArg (fun b:VenueProgram.Registered=>b.roof G) eq)⟩

include before tail cut in
theorem ordinary_ports_at (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area):
    let assigned:=VenueProgram.Registered.atAge G S op g k i p frozen f drift degree payload seats root ports ordinary
    DatePorts.ordinaryPorts ports ticket op g frozen p f drift degree payload seats root ordinary=assigned.next G ∧
      (v).countAddr root=assigned.selector G ∧ (v).fullEnd root=assigned.roof G:=
  ordinaryPorts_public X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary paths

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
