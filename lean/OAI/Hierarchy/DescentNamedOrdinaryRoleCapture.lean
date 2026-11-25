import OAI.Hierarchy.DescentNamedOrdinaryRoleInputs
import OAI.Hierarchy.DescentOrdinaryCapturedRoleStock

namespace OAI
/-! A single original ordinary date acquires the true stored role tuple after the counter,
from its prior archive and sampled hardware input. -/
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

local notation "L" => (v).paletteShape
open ThreeFlat.RAM PhysicalProcedure
set_option maxHeartbeats 1200000 in
theorem ordinary_captured_role {w} (age : i<S.length) (radix : S.radix=2^k)
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
    (chart : (v).SignedChart) (blk : (rc₀).blocks=(v).material.blocks)
    (pg : Fin (7*(v).vector.operands)) (admission : (v).TicketAdmission floor w chart (A) (match₀) pg)
    (total : (v).origin.preparationWords=(v).originControlWords+(v).originMouthWords+(v).rootSourceSize)
    (endFit : (v).endAddress floor<2^w) (wide : (rc₀).lanes*DescentPackedOperand.unit (rc₀).size≤w/2)
    (paid : NativePhase w) (charge : PhysicalOrdinary.Span paid ((v).endAddress floor) ((v).rasterEnd floor))
    (columns : StageVenueTail.Sources) (survivors : (v).ResultRoom floor columns w)
    (refRadix : (vx₀).radix=2^(v).reference.k)
    (good : (refs₀).Room w vecAt) (primitive : (v).PrimitiveRoom floor (A) w)
    (capacity : (L).Capacity ((v).primitiveSources floor (A) (match₀) refRadix))
    (hosts : (L).hosts=(v).bornBook.hosts) (og : (L).oldGroups=(v).bornBook.groups)
    (top : ((v).area.matcher (v).old floor).layout.topology.Fits w ((v).primitiveEnd floor))
    (high : (v).returnedEnd floor<2^w) :
    let groups : G₀=(vx₀).groups*(vx₀).radix:=(dims₀ age radix).2.2.2
    let data₀:=(A).venueWord (v) parts active hubs peer width
    let selected:Val₀ (v).reference.nameBits (v).reference.countBits:=fun col low=>
      groupValues groups ((A).registeredValues (v) form floor (match₀) old parts roles (Gather.reaching peer)
        data₀ names ranks col low)
    let original : Fin (L).blocks → Fin (L).hosts → Fin (L).oldGroups → Cell ((L).primitiveBits*(L).oldNodes) :=fun x=>rowsAt (hosts.trans form.hosts) (og.trans form.groups)
      (rfl : (A).roleBits*(v).reference.oldNodes=(L).primitiveBits*(v).reference.oldNodes)
      (DescentOrdinaryHostPad.extend H₀ (roles (x.cast (match₀).oldBlocks.symm)))
    let origin : Fin (L).blocks → Fin (L).successors → Fin (L).groups → Cell ((L).originBits*(L).newNodes) :=fun x=>DescentScalarBookReshape.book (fun l h g=>
      selection (v).originCandidates (v).resolver.nodes (v).originBits (marked (selected pg l) h g)) (x.cast refRadix.symm)
    let next : Fin (L).hosts → Fin (L).ports → Option (Fin (L).hosts) := PhysicalOrdinary.primitiveRoster (hosts.trans form.hosts) (match₀).paths.symm (DescentSortedRoster.indexed (Gather.reaching peer))
    let st:=(v).paletteStock floor (A) (match₀) original ((A).nativeChips (v) form.toBirthShape parts) hosts og origin next
    let prep:=(v).nativeTicketPreparation floor w chart (A) (match₀) (sh) blk pg
    let src:=(v).nativeTicketExpr floor chart (A) (match₀) (sh) blk
    let args:=((v).argumentPhaseAfterSigned floor (A) (match₀) src prep ((A).chip_fits (v) floor safe (match₀)) (sh) endFit wide).image m
    let post:=((v).returnPhase floor columns w survivors).image (paid.image args)
    (L).Published st (DatePorts.ordinary (v) floor).archive.roles.bank
      (((v).counter floor w).image (((v).primitiveUpdate floor (A) (match₀) refRadix w).image post)):=by
  intro groups data₀ selected original origin next st prep src args post
  obtain ⟨a,b,c,d,e⟩:=(v).routed_order floor
  have before:vecAt<2^w:=(a.trans (b.trans (c.trans (d.trans e)))).trans_lt endFit
  have current:=ordinary_role_inputs prior ticket op gain tail p f drift degree payload seats root ordinary age radix
      m safe form old parts roles oldPitch panelPitch rolePitch lower oldRows panel roleLo roleRoom roleRows
      active hubs peer actors act one near width names ranks before
  apply (v).captured_role_stock floor w chart (A) (match₀) (sh) blk pg admission total
      ((A).chip_fits (v) floor safe (match₀)) endFit wide paid charge columns survivors m refRadix safe
      good primitive capacity form.toBirthShape hosts og rfl rfl top high roles rolePitch
      (fun x=>⟨roleLo x,roleRoom x,roleRows x⟩) parts panelPitch panel _ current.2.1 current.2.2
      (fun l=>selected pg l) (current.1 pg)

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
