import OAI.Hierarchy.DescentNamedCutWalkRoster
import OAI.Hierarchy.DescentNamedOrdinaryPublishedTags
import OAI.Hierarchy.DescentNamedCutArchiveHeaders
import OAI.Hierarchy.DescentDatedBookedChip

namespace OAI
/-! The registered W sheets, original sorted paths and newborn chip on one named cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 7000
set_option cleanup.letToHave false

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


set_option quotPrecheck false
variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books₀" => OrdinaryBooks.atDate G S op g k i p tailBits drift degree payload seats ports
local notation "base₀" => (books₀).onTicket ticket g tailBits p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "floor₀" => (base₀).stageStart root
local notation "v₀" => DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "entry₀" => (base₀).registeredEntry ports floor₀
local notation "mat₀" => (base₀).registered_match ports floor₀ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open scoped Classical Fin.CommRing
local notation "sh₀" => (base₀).registered_geometry ports floor₀
local notation "rc₀" => (v₀).resolver
local notation "vx₀" => (v₀).vector
local notation "bn₀" => (v₀).bornBook
local notation "g₀" => (v₀).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v₀).vectorStart floor₀
local notation "mouthEnd₀" => (v₀).originMouthEnd floor₀
local notation "headerEnd" => (v₀).operandHeaderEnd floor₀
local notation "e₀" => (v₀).material
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short
local notation "ps₀" => (v₀).operandPathStart floor₀
local notation "refs₀" => ((entry₀).directory (v₀) floor₀ (mat₀)).refs
local notation "Val₀" => References.Rows (v₀).vector (v₀).reference.degree (v₀).reference.k (v₀).reference.oldNodes
  (v₀).reference.capacity ((rc₀).size+2)
local notation "dims₀" => DatePorts.ordinary_header_dimensions ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (entry₀).clip.venue.socket.degree→Option (Fin H₀)

include before tail cut in
theorem cut_tagged_shelf {w} (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
    (pg : Fin (vx₀).pageCount) (m : Memory w) (safe : (entry₀).Room (v₀) floor₀ w)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (old : Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts (entry₀).clip.venue.socket)
    (roles : Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (oldPitch : 0<(entry₀).previous.lanes) (panelPitch : 0<(entry₀).clip.panelPitch) (rolePitch : 0<(entry₀).rolePitch)
    (lower : ∀x p,(previousBank (entry₀).previous (entry₀).previousBase x p).Fits w ((v₀).signedEnd floor₀))
    (oldRows : ∀x p,Reads (previousBank (entry₀).previous (entry₀).previousBase x p) (old p x) (entry₀).previous.lanes m)
    (panel : Reads (entry₀).venue.panel (fun h g=>DepotRAM.combine (entry₀).clip.venue.socket (parts h g)) (entry₀).clip.panelPitch m)
    (roleLo : ∀x,((entry₀).role x).base+((entry₀).role x).size≤(v₀).signedEnd floor₀) (roleRoom : ∀x,(entry₀).previous.hosts*chunks G₀ (entry₀).rolePitch≤((entry₀).role x).size)
    (roleRows : ∀x,Reads ((entry₀).role x) (roles x) (entry₀).rolePitch m)
    (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers) (actors : 0<(entry₀).clip.actorPitch)
    (act : Reads (entry₀).venue.actors active (entry₀).clip.actorPitch m)
    (one : ∀h : Fin H₀,m ((entry₀).venue.hub.base+h.val)=((hubs h).val:Word w))
    (near : ∀h j,m ((entry₀).venue.adjacency.base+(h.val*(entry₀).clip.venue.socket.degree+j.val))=(number (peer h j):Word w))
    (oldR : Fin (e₀).oldHosts→Fin (fmt₀).degree→Option (Fin (e₀).oldHosts))
    (hostsFit : (e₀).oldHosts<2^w)
    (priorRead : ∀h j,m (ports.io.roster.base+h.val*(fmt₀).degree+j.val)=(number (oldR h j):Word w))
    (typed : BookTags (l:=(entry₀).previous) (fun x p=>old p x))
    (pitch : 0<W₀) (space : vecAt<2^w) :
    let shapes:=ordinary_publication_shape X G S br ticket before tail cut ports op tailBits drift degree payload seats
      root ordinary previous (congrArg (fun n : ℕ=>n-2) archive.digits)
    let form:=shapes.1
    let width:=shapes.2.1
    let names:=shapes.2.2.1
    let ranks:=shapes.2.2.2
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(entry₀).venueWord (v₀) parts active hubs peer width
    let oldBooks : Val₀ (v₀).reference.nameBits (v₀).reference.countBits:=fun col low=>
      groupValues groups ((entry₀).registeredValues (v₀) form floor₀ (mat₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    let chip:=(entry₀).nativeChips (v₀) form.toBirthShape parts
    let installed:=(entry₀).mountedTape (v₀) floor₀ m
    (∀p q,ScalarOperand.Measured (((refs₀) p) q) (oldBooks p q)
      (rc₀).nodes W₀ vecAt installed) ∧
    BookTags ((v₀).registeredOperandBooks (sh₀) oldBooks) ∧
    (∀q,HEq (oldBooks pg q).walks (Gather.reaching oldR)) ∧
    (bn₀).rows≤((entry₀).chipBank (v₀) floor₀).size ∧
    Reads ((entry₀).chipBank (v₀) floor₀) chip (bn₀).lanes installed :=by
  intro shapes form width names ranks groups data₀ oldBooks chip installed
  have books:=DatePorts.ordinary_published_tag_rows ports ticket op g tailBits p f drift degree payload seats
    root ordinary age radix m safe form old parts roles oldPitch panelPitch rolePitch lower oldRows panel roleLo roleRoom
    roleRows active hubs peer actors act one near width names ranks typed pitch space
  have slots:=(entry₀).mounted_header_chip (v₀) floor₀ m form.toBirthShape (mat₀) safe panelPitch parts panel space
  have walks:=registered_walk_identity (radix := radix) X G S ticket ports op tailBits drift degree payload seats root ordinary
    age pg m form old parts roles active hubs peer oldR hostsFit ports.io.roster rfl
    (fun h j => by simpa only [Nat.add_assoc] using near h j) priorRead width names ranks
  exact ⟨books.1,books.2,walks,slots.2.1,slots.2.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
