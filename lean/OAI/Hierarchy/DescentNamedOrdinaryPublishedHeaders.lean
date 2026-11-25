import OAI.Hierarchy.DescentNamedOrdinaryPanelHeaders
import OAI.Hierarchy.DescentOrdinaryPublishedRows

namespace OAI
/-! # Ordinary header values from actual preceding banks and the matched donor panel -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor

local notation "rc₀" => (v).resolver
local notation "vx₀" => (v).vector
local notation "bn₀" => (v).bornBook
local notation "g₀" => (v).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v).vectorStart floor
local notation "mouthEnd₀" => (v).originMouthEnd floor
local notation "headerEnd" => (v).operandHeaderEnd floor
local notation "e₀" => (v).material
local notation "fmt₀" => (v).ticket.depotShape (v).short
local notation "ps₀" => (v).operandPathStart floor
local notation "refs₀" => ((A).directory (v) floor (match₀)).refs
local notation "Val₀" => References.Rows (v).vector (v).reference.degree (v).reference.k (v).reference.oldNodes
  (v).reference.capacity ((rc₀).size+2)
local notation "dims₀" => ordinary_header_dimensions prior ticket op gain tail p f drift degree payload seats root ordinary
local notation "H₀" => (A).clip.venue.hosts
local notation "G₀" => (A).clip.venue.groups
local notation "pop₀" => (A).population (v) floor
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(A).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (A).clip.venue.socket.degree→Option (Fin H₀)

theorem ordinary_published_headers {w} (age : i<S.length) (radix : S.radix=2^k)
    (pg : Fin (vx₀).pageCount) (m : Memory w) (safe : (A).Room (v) floor w)
    (form : (A).InputShape (v))
    (old : Pages (A).previous.operands→Fin (A).previous.blocks→Fin (A).previous.hosts→Fin (A).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (A).previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts (A).clip.venue.socket)
    (roles : Fin (A).previous.blocks→Fin (A).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (oldPitch : 0<(A).previous.lanes) (panelPitch : 0<(A).clip.panelPitch) (rolePitch : 0<(A).rolePitch)
    (lower : ∀x p,(previousBank (A).previous (A).previousBase x p).Fits w ((v).signedEnd floor))
    (oldRows : ∀x p,Reads (previousBank (A).previous (A).previousBase x p) (old p x) (A).previous.lanes m)
    (panel : Reads (A).venue.panel (fun h g=>DepotRAM.combine (A).clip.venue.socket (parts h g)) (A).clip.panelPitch m)
    (roleLo : ∀x,((A).role x).base+((A).role x).size≤(v).signedEnd floor) (roleRoom : ∀x,(A).previous.hosts*chunks G₀ (A).rolePitch≤((A).role x).size)
    (roleRows : ∀x,Reads ((A).role x) (roles x) (A).rolePitch m)
    (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers) (actors : 0<(A).clip.actorPitch)
    (act : Reads (A).venue.actors active (A).clip.actorPitch m)
    (one : ∀h : Fin H₀,m ((A).venue.hub.base+h.val)=((hubs h).val:Word w))
    (near : ∀h j,m ((A).venue.adjacency.base+(h.val*(A).clip.venue.socket.degree+j.val))=(number (peer h j):Word w))
    (width : Packed.bits (A).clip.venue.names*(A).clip.actorCount=(v).reference.nameBits*(v).reference.actors)
    (names : (pop₀).nameBits=(v).reference.nameBits) (ranks : (pop₀).donors=(v).reference.donors)
    (good : (refs₀).Room w vecAt)
    (panelSize : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤(A).venue.panel.size)
    (panelWord : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (earlier : PriorHeader.endAddress (e₀).oldHosts (e₀).groups (e₀).lanes (fmt₀).degree ((v).donorEnd floor)≤ps₀)
    (before : vecAt<2^w) (space : headerEnd<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(A).venueWord (v) parts active hubs peer width
    let oldBooks : Val₀ (v).reference.nameBits (v).reference.countBits:=fun col low=>
      groupValues groups ((A).registeredValues (v) form floor (match₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    let chip:=(A).nativeChips (v) form.toBirthShape parts
    let dims:=dims₀ age radix
    let home:=dims.2.1
    let group:=dims.2.2.2
    let word : (bn₀).bits=(rc₀).size+2:=rfl
    let mouthRows:=(v).headerMouthRows floor (A) (match₀) oldBooks home group word
    let first:=((refs₀).phase w vecAt).image ((A).mountedTape (v) floor m)
    let here:=((v).originAndMouth floor w (A) (match₀) (v).operandShortBits ((refs₀) pg)).image first
    let last:=((v).operandEarlyPhase floor w A).image here
    (∀j f,Held g₀ headerEnd last ((v).originAt floor (v).operandShortBits (sh) j f) ((v).originHeaderValue (sh) (oldBooks pg) j f)) ∧
    (∀j f,Held g₀ headerEnd last ((v).oldHeaderAt floor j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v).previousHeaderValue (sh) oldBooks j f h k))) ∧
    ∀j f,Held g₀ headerEnd last ((v).mouthAt floor (A) (match₀) (sh) j f)
      (fun h k=>ScalarOperand.take (((rc₀).index.symm j).2.1) ((v).mouthHeaderValue floor (A) (match₀) (sh) mouthRows chip home group j f h k)) :=by
  intro groups data₀ oldBooks
  apply ordinary_panel_headers prior ticket op gain tail p f drift degree payload seats root ordinary age radix pg
    oldBooks m safe form.toBirthShape panelPitch parts panel good _ panelSize panelWord earlier space
  intro col low
  apply group_measured groups
  exact (A).published_rows (v) form floor (match₀) m safe before old parts roles oldPitch panelPitch rolePitch
    lower oldRows panel roleLo roleRoom roleRows active hubs peer actors act one near width names ranks col low

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
