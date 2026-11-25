import OAI.Hierarchy.DescentNamedOrdinaryPublishedPointers
import OAI.Hierarchy.DescentDatedRegisteredTagRows

namespace OAI
/-! The occupied W roster and its native tag page after a reset or an ordinary predecessor. -/
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

theorem ordinary_published_tags {w} (age : i<S.length) (radix : S.radix=2^k)
    (m : Memory w) (_safe : (A).Room (v) floor w)
    (form : (A).InputShape (v))
    (old : Pages (A).previous.operands→Fin (A).previous.blocks→Fin (A).previous.hosts→Fin (A).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (A).previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts (A).clip.venue.socket)
    (roles : Fin (A).previous.blocks→Fin (A).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (_oldPitch : 0<(A).previous.lanes) (_panelPitch : 0<(A).clip.panelPitch) (_rolePitch : 0<(A).rolePitch)
    (_lower : ∀x p,(previousBank (A).previous (A).previousBase x p).Fits w ((v).signedEnd floor))
    (_oldRows : ∀x p,Reads (previousBank (A).previous (A).previousBase x p) (old p x) (A).previous.lanes m)
    (_panel : Reads (A).venue.panel (fun h g=>DepotRAM.combine (A).clip.venue.socket (parts h g)) (A).clip.panelPitch m)
    (_roleLo : ∀x,((A).role x).base+((A).role x).size≤(v).signedEnd floor) (_roleRoom : ∀x,(A).previous.hosts*chunks G₀ (A).rolePitch≤((A).role x).size)
    (_roleRows : ∀x,Reads ((A).role x) (roles x) (A).rolePitch m)
    (active : Active) (hubs : Fin H₀→Cell 1) (peer : RealPeers) (_actors : 0<(A).clip.actorPitch)
    (_act : Reads (A).venue.actors active (A).clip.actorPitch m)
    (_one : ∀h : Fin H₀,m ((A).venue.hub.base+h.val)=((hubs h).val:Word w))
    (_near : ∀h j,m ((A).venue.adjacency.base+(h.val*(A).clip.venue.socket.degree+j.val))=(number (peer h j):Word w))
    (width : Packed.bits (A).clip.venue.names*(A).clip.actorCount=(v).reference.nameBits*(v).reference.actors)
    (names : (pop₀).nameBits=(v).reference.nameBits) (ranks : (pop₀).donors=(v).reference.donors)
    (typed : BookTags (l:=(A).previous) (fun x p=>old p x))
    (_pitch : 0<W₀) (_before : vecAt<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(A).venueWord (v) parts active hubs peer width
    let oldBooks : Val₀ (v).reference.nameBits (v).reference.countBits:=fun col low=>
      groupValues groups ((A).registeredValues (v) form floor (match₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    BookTags ((v).registeredOperandBooks (sh) oldBooks) :=by
  intro groups data₀ oldBooks
  apply (v).registered_input_tags (sh) oldBooks
  · intro arg low block h g node
    have pageEq := pointer_page_cast (sh).operands arg 0
    change (ScalarOperand.take node ((groupValues groups ((A).registeredValues (v) form floor
      (match₀) old parts roles (Gather.reaching peer) data₀ names ranks
      ((v).registeredPointerPages (sh) arg 0) low)).old block h g)).val ≤ 2
    let values := (A).registeredValues (v) form floor (match₀) old parts roles
      (Gather.reaching peer) data₀ names ranks ((v).registeredPointerPages (sh) arg 0) low
    have moved := old_group_cell groups values block h g
    refine (congrArg (fun word => (ScalarOperand.take node word).val) moved).le.trans ?_
    change (ScalarOperand.take node ((A).oldInput (v) form floor (match₀) old
      ((v).registeredPointerPages (sh) arg 0) block h (g.cast groups.symm))).val ≤ 2
    rw [show (v).registeredPointerPages (sh) arg 0 = _ from pageEq]
    exact (A).registered_old_input_tag (v) form floor (match₀) old typed rfl
      (arg.cast (sh).operands) block h (g.cast groups.symm) node
  · intro arg low block seat arm h g
    have wide : 2≤(bn₀).bits:=Nat.le_add_left 2 (rc₀).size
    have ok:=(A).registered_born_input_typed (v) form floor (match₀) wide parts (arg.cast (sh).operands)
      block seat arm h (g.cast groups.symm)
    have pageEq := pointer_page_cast (sh).operands arg 0
    change ((groupValues groups ((A).registeredValues (v) form floor
      (match₀) old parts roles (Gather.reaching peer) data₀ names ranks
      ((v).registeredPointerPages (sh) arg 0) low)).born block seat arm h g).val ≤ 2
    let values := (A).registeredValues (v) form floor (match₀) old parts roles
      (Gather.reaching peer) data₀ names ranks ((v).registeredPointerPages (sh) arg 0) low
    have moved := born_group_cell groups values block seat arm h g
    refine (congrArg Fin.val moved).le.trans ?_
    change ((A).bornInput (v) form floor (match₀) parts ((v).registeredPointerPages (sh) arg 0)
      block seat arm h (g.cast groups.symm)).val ≤ 2
    rw [show (v).registeredPointerPages (sh) arg 0 = _ from pageEq]
    exact kind_of_typed ok

theorem ordinary_published_tag_rows {w} (age : i<S.length) (radix : S.radix=2^k)
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
    (typed : BookTags (l:=(A).previous) (fun x p=>old p x))
    (pitch : 0<W₀) (before : vecAt<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(A).venueWord (v) parts active hubs peer width
    let oldBooks : Val₀ (v).reference.nameBits (v).reference.countBits:=fun col low=>
      groupValues groups ((A).registeredValues (v) form floor (match₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    (∀p q,ScalarOperand.Measured ((refs₀) p q) (oldBooks p q) (rc₀).nodes W₀ vecAt
      ((A).mountedTape (v) floor m)) ∧ BookTags ((v).registeredOperandBooks (sh) oldBooks) :=by
  intro groups data₀ oldBooks
  refine ⟨?_,?_⟩
  · intro col low
    apply group_measured groups
    exact (A).published_rows (v) form floor (match₀) m safe before old parts roles oldPitch panelPitch rolePitch
      lower oldRows panel roleLo roleRoom roleRows active hubs peer actors act one near width names ranks col low
  · exact ordinary_published_tags prior ticket op gain tail p f drift degree payload seats root ordinary age radix m safe
      form old parts roles oldPitch panelPitch rolePitch lower oldRows panel roleLo roleRoom roleRows active hubs peer
      actors act one near width names ranks typed pitch before

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
