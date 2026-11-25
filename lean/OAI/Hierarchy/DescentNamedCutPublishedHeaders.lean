import OAI.Hierarchy.DescentNamedCutTicketAdmission
import OAI.Hierarchy.DescentNamedOrdinaryPublishedHeaders
import OAI.Hierarchy.DescentOrdinaryPreparedLimit

namespace OAI
/-! The thirteen native ordinary ticket headers at a cut of the named branch. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
set_option cleanup.letToHave false
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
/-- The venue decoder sees the same number of bits per tag and the same number
of actor slots as the controller which emitted it. -/
theorem ordinary_publication_arities :
    Packed.bits (entry₀).clip.venue.names=(v₀).reference.nameBits ∧
    (entry₀).clip.actorCount=(v₀).reference.actors :=by
  let date:=DonorDate.atDate G S g k i p
  have chosen : ticket.donorDate=date:=donor_date_eq X G S br ticket before tail cut
  have deg : prior.placement.degree=date.degree:=congrArg DonorDate.degree chosen
  have capacity : prior.placement.cap=date.cap:=congrArg DonorDate.cap chosen
  have sites : (entry₀).clip.venue.names=(v₀).vector.lows:=by
    change (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots prior.placement.degree=
      (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots date.degree
    rw [deg]
  have labels : Packed.bits (v₀).vector.lows=(v₀).reference.nameBits:=rfl
  have count : (entry₀).clip.actorCount=(v₀).reference.actors:=by
    change ((prior.placement.degree+1)^4*2^k)*(1+prior.placement.cap*6)=
      ((prior.placement.degree+1)^4*2^k)*(1+date.cap*6)
    rw [capacity]
  exact ⟨(congrArg Packed.bits sites).trans labels,count⟩

include before tail cut in
/-- The interval bit budget is fixed for the entire path. The incoming argument count
and node count continue to come from the actual preceding archive. -/
theorem ordinary_publication_shape (previous : ports.venue.groups=S.groupCount i)
    (bitsAt : ports.operandBits-2=DescentOperandWidth.recordBits G S k tailBits drift degree p-2) :
    (entry₀).InputShape (v₀) ∧
    Packed.bits (entry₀).clip.venue.names*(entry₀).clip.actorCount=(v₀).reference.nameBits*(v₀).reference.actors ∧
    (pop₀).nameBits=(v₀).reference.nameBits ∧ (pop₀).donors=(v₀).reference.donors :=by
  let date:=DonorDate.atDate G S g k i p
  have chosen : ticket.donorDate=date:=donor_date_eq X G S br ticket before tail cut
  have deg : prior.placement.degree=date.degree:=congrArg DonorDate.degree chosen
  have short : (v₀).short=max (k+3) (Nat.clog 2 (prior.placement.degree+1)):=by
    change max (k+3) (Nat.clog 2 (date.degree+1))=_
    rw [deg]
  have socket : (entry₀).clip.venue.socket=date.format:=by
    change ticket.depotShape (v₀).short=date.format
    rw [short,←chosen]
    rfl
  have chip : DepotRAM.outputBits (entry₀).clip.venue.socket=(v₀).bornBook.chipBits:=by
    rw [socket]
    rfl
  have priorWidth : DescentOrdinaryPriorRetile.digits (entry₀).previous=(v₀).reference.bits*(v₀).reference.oldNodes:=by
    change ((ports.operandBits-2)+2)*ports.nodes=
      ((DescentOperandWidth.recordBits G S k tailBits drift degree p-2)+2)*ports.nodes
    rw [bitsAt]
  have form : (entry₀).InputShape (v₀):=⟨⟨rfl,rfl,chip⟩,previous.symm,priorWidth,rfl⟩
  have decoding : Packed.bits (entry₀).clip.venue.names=(v₀).reference.nameBits ∧
      (entry₀).clip.actorCount=(v₀).reference.actors:=
    ordinary_publication_arities X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  exact ⟨form,congrArg₂ (·*·) decoding.1 decoding.2,rfl,rfl⟩

include before tail cut in
theorem cut_published_headers {w} (age : i<S.length) (chart : (v₀).SignedChart)
    (previous : ports.venue.groups=S.groupCount i) (lanes : 0<(v₀).vector.lanes)
    (pg : Fin (vx₀).pageCount) (m : Memory w) (safe : (entry₀).Room (v₀) floor₀ w)
    (form : (entry₀).InputShape (v₀))
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
    (width : Packed.bits (entry₀).clip.venue.names*(entry₀).clip.actorCount=(v₀).reference.nameBits*(v₀).reference.actors)
    (names : (pop₀).nameBits=(v₀).reference.nameBits) (ranks : (pop₀).donors=(v₀).reference.donors)
    (endFit : (v₀).endAddress floor₀<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(entry₀).venueWord (v₀) parts active hubs peer width
    let oldBooks : Val₀ (v₀).reference.nameBits (v₀).reference.countBits:=fun col low=>
      groupValues groups ((entry₀).registeredValues (v₀) form floor₀ (mat₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    let chip:=(entry₀).nativeChips (v₀) form.toBirthShape parts
    let dims:=dims₀ age radix
    let home:=dims.2.1
    let group:=dims.2.2.2
    let word : (bn₀).bits=(rc₀).size+2:=rfl
    let mouthRows:=(v₀).headerMouthRows floor₀ (entry₀) (mat₀) oldBooks home group word
    let first:=((refs₀).phase w vecAt).image ((entry₀).mountedTape (v₀) floor₀ m)
    let here:=((v₀).originAndMouth floor₀ w (entry₀) (mat₀) (v₀).operandShortBits ((refs₀) pg)).image first
    let last:=((v₀).operandEarlyPhase floor₀ w (entry₀)).image here
    (∀j f,Held g₀ headerEnd last ((v₀).originAt floor₀ (v₀).operandShortBits (sh₀) j f) ((v₀).originHeaderValue (sh₀) (oldBooks pg) j f)) ∧
    (∀j f,Held g₀ headerEnd last ((v₀).oldHeaderAt floor₀ j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v₀).previousHeaderValue (sh₀) oldBooks j f h k))) ∧
    ∀j f,Held g₀ headerEnd last ((v₀).mouthAt floor₀ (entry₀) (mat₀) (sh₀) j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v₀).mouthHeaderValue floor₀ (entry₀) (mat₀) (sh₀) mouthRows chip home group j f h k)) :=by
  have observed:=signed_stage_eq X G S br ticket before tail cut (NativePitch.incomingHosts S (i+1))
  have field : (v₀).material.fieldBits=(v₀).signedLayout.fieldBits:=congrArg SignedStage.fieldBits observed.symm
  obtain ⟨capacity,word,priorHeaders⟩:=DatePorts.ordinary_ticket_panel_fields ports ticket op g tailBits p f drift degree
    payload seats root ordinary chart safe field (signed_source_capacity X G S br ticket before tail cut)
  have allFit:=((base₀).registered_prepared_limit ports floor₀).trans_lt endFit
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=(v₀).ticket_source_order floor₀
  have headFit:=r₇.trans_lt (r₈.trans_lt (r₉.trans_lt allFit))
  have routeFit:=r₁.trans_lt (r₂.trans_lt (r₃.trans_lt (r₄.trans_lt (r₅.trans_lt (r₆.trans_lt headFit)))))
  have gather:=DatePorts.ordinary_gather_room ports ticket op g tailBits p f drift degree payload seats root ordinary
    safe previous lanes routeFit
  exact DatePorts.ordinary_published_headers ports ticket op g tailBits p f drift degree payload seats root ordinary
    age radix pg m safe form old parts roles oldPitch panelPitch rolePitch lower oldRows panel roleLo roleRoom roleRows
    active hubs peer actors act one near width names ranks gather capacity word priorHeaders
    (((v₀).vector_before floor₀).trans_lt routeFit) headFit

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
