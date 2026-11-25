import OAI.Hierarchy.DescentNamedOrdinaryPublishedTags

namespace OAI
/-! Native ordinary primitive capture receives its W regulator rows and full four-hop
directory from the actual previous role, operand, actor, hub, peer and signed-chip banks. -/
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

theorem ordinary_role_inputs {w} (age : i<S.length) (radix : S.radix=2^k)
    (m : Memory w) (safe : (A).Room (v) floor w)
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
    (before : vecAt<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(A).venueWord (v) parts active hubs peer width
    let selected:Val₀ (v).reference.nameBits (v).reference.countBits:=fun col low=>
      groupValues groups ((A).registeredValues (v) form floor (match₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    let real:=DescentSortedRoster.indexed (Gather.reaching peer)
    let fieldBank:=(A).clip.fieldBank ((v).signedEnd floor)
    (∀p q,ScalarOperand.Measured ((refs₀) p q) (selected p q) (rc₀).nodes W₀ vecAt ((A).mountedTape (v) floor m)) ∧
    Mounted ((A).ports (v) floor) real ((A).clippedTape (v) floor m) G₀ (A).clip.working ∧
    Accessible ((A).ports (v) floor) fieldBank H₀ G₀ (A).clip.working w ((A).priorStart (v) floor):=by
  intro groups data₀ selected real fieldBank
  obtain ⟨_,roster,able⟩:=(A).clip.issued (A).venue ((v).signedEnd floor) m safe.venue panelPitch actors
    parts active hubs peer panel act one near
  have fieldRoom:fieldBank.Fits w ((A).priorStart (v) floor):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt safe.venue.space,le_rfl⟩
  refine ⟨?_,roster,able fieldBank fieldRoom (A).clip.core.rowRoom⟩
  intro col low
  apply group_measured groups
  exact (A).published_rows (v) form floor (match₀) m safe before old parts roles oldPitch panelPitch rolePitch
    lower oldRows panel roleLo roleRoom roleRows active hubs peer actors act one near width names ranks col low

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
