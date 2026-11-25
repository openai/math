import OAI.Hierarchy.DescentNamedCutResolverKeys
import OAI.Hierarchy.DescentNamedOrdinaryRoleCapture
import OAI.Hierarchy.DescentRegisteredHeaderFrames
import OAI.Hierarchy.DescentPrimitiveBankFloor
import OAI.Hierarchy.DescentNamedPrimitiveCharge
import OAI.Hierarchy.DescentRegisteredArgumentGatherRoom

namespace OAI
/-! The primitive archive rows returned by the native program on the selected ordinary cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
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

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "wired" m:arg => DatePorts.ordinarySignedMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m


local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

variable {original : Memory w} (stores : CutStores (radix:=radix) (X:=X) (G:=G) (S:=S) (k:=k) (f:=f) (g:=g) (p:=p) (prior:=prior) (ticket:=ticket) (ports:=ports) (op:=op)
  (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
  (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) original)
local notation "L₀" => (v₀).paletteShape

variable {X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec}

include stores in
private theorem cut_primitive_groups : (L₀).oldGroups=(v₀).bornBook.groups :=by
  change (vx₀).groups*2^(v₀).reference.k=(v₀).bornBook.groups
  rw [←code.radix]
  exact stores.groups.symm

private noncomputable def stockWithBooks (values : Val₀ (v₀).reference.nameBits (v₀).reference.countBits) : (L₀).Stock :=
  let past : Fin (L₀).blocks → Fin (L₀).hosts → Fin (L₀).oldGroups → Cell ((L₀).primitiveBits*(L₀).oldNodes) :=fun x=>rowsAt (stores.primitiveHosts.trans stores.inputs.hosts)
    ((cut_primitive_groups stores).trans stores.inputs.groups)
    (rfl : (entry₀).roleBits*(v₀).reference.oldNodes=(L₀).primitiveBits*(v₀).reference.oldNodes)
    (DescentOrdinaryHostPad.extend H₀ (stores.roles (x.cast (mat₀).oldBlocks.symm)))
  let origin : Fin (L₀).blocks → Fin (L₀).successors → Fin (L₀).groups → Cell ((L₀).originBits*(L₀).newNodes) :=fun x=>DescentScalarBookReshape.book (fun l a b=>
    selection (v₀).originCandidates (v₀).resolver.nodes (v₀).originBits (marked (values page₀ l) a b))
    (x.cast code.radix.symm)
  let next : Fin (L₀).hosts → Fin (L₀).ports → Option (Fin (L₀).hosts) := PhysicalOrdinary.primitiveRoster (stores.primitiveHosts.trans stores.inputs.hosts)
    (mat₀).paths.symm (DescentSortedRoster.indexed (Gather.reaching stores.rotor))
  (v₀).paletteStock floor₀ (entry₀) (mat₀) past ((entry₀).nativeChips (v₀) stores.inputs.toBirthShape stores.parts)
    stores.primitiveHosts (cut_primitive_groups stores) origin next

include stores in
/-- The prior archive, measured chip, origin and rotor used by the primitive instruction. -/
noncomputable def cut_primitive_stock : (L₀).Stock :=
  stockWithBooks stores stores.books

local notation "date₀" => DonorDate.atDate G S g k i p
local notation "rotation" => ((date₀).schedule payload seats (v₀).bitsPerField).rotationEnd ports.io.roster floor₀
local notation "meter" => (date₀).counter payload rotation headerBase
local notation "final" => DatePorts.ordinaryOutput ports ticket op g tailBits p f drift degree payload seats root ordinary
  w shelfHeader headerBase pos code exec original

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
include before tail cut in
/-- The counted output of this issued date contains every emitted primitive row. -/
theorem cut_primitive_published (age : i<S.length) (low : headerBase<root)
    (room : (v₀).PrimitiveRoom floor₀ (entry₀) w)
    (capacity : (L₀).Capacity ((v₀).primitiveSources floor₀ (entry₀) (mat₀) code.radix)) :
    (L₀).Published (cut_primitive_stock stores) (DatePorts.ordinary (v₀) floor₀).archive.roles.bank final:=by
  obtain ⟨_,a,b,c,d⟩:=(v₀).routed_order floor₀
  have routed:=(a.trans (b.trans (c.trans d))).trans_lt code.endFit
  have gather:=DatePorts.ordinary_gather_room ports ticket op g tailBits p f drift degree payload seats root ordinary
    stores.entryFits stores.previousGroups stores.admission.lanes routed
  have published:=DatePorts.ordinary_captured_role ports ticket op g tailBits p f drift degree payload seats root ordinary
    age radix (wired original) stores.entryFits stores.inputs stores.old stores.parts stores.roles
    stores.oldPitch stores.board.live stores.rolePitch stores.oldBanks stores.oldRead stores.panel
    stores.roleLo stores.roleRoom stores.roleRead stores.active stores.hubs stores.rotor stores.actorsPositive
    stores.actors stores.flags stores.peers stores.width stores.names stores.ranks code.signed code.blocks page₀
    stores.admission ((base₀).registered_reservation ports floor₀) code.endFit code.packed
    (steps₀).paid exec.late.funded ((v₀).reachedSources floor₀) code.result code.radix gather room capacity
    stores.primitiveHosts (cut_primitive_groups stores) exec.topology exec.limit
  have frame:=ordinary_header_frames X G S br ticket before tail cut op tailBits drift degree payload seats root
    ports ordinary headerBase low
  have lastTable:(v₀).finalChart.out ((v₀).metaEnd floor₀)≤(v₀).operandEnd floor₀:=by
    rw [PhysicalOrdinary.operandEnd,code.result.geometry]
    exact (Nat.le_add_right ..).trans (((v₀).finalChart.order _).2.2)
  intro x l
  let current:=(steps₀).arguments.image (wired original)
  let emitted:=((v₀).returnPhase floor₀ ((v₀).reachedSources floor₀) w code.result).image ((steps₀).paid.image current)
  let counted:=((v₀).counter floor₀ w).image ((steps₀).primitive.image emitted)
  let bank:=(DatePorts.ordinary (v₀) floor₀).archive.roles.bank x.val
  let j:=bank.base+(row (L₀).successors (L₀).groups (L₀).nextLanes l).val
  have after:(meter).endAddr≤j:=frame.1.trans (lastTable.trans
    (((v₀).primitive_bank_lower ((v₀).operandEnd floor₀) x).trans (Nat.le_add_right ..)))
  have saved:=(meter).counter_frame counted exec.counter j (ne_of_gt (frame.2.trans_le after)) (.inr after)
  change (meter).image counted j = _
  rw [saved]
  let decoded : Val₀ (v₀).reference.nameBits (v₀).reference.countBits :=fun col low=>groupValues stores.groups
    ((entry₀).registeredValues (v₀) stores.inputs floor₀ (mat₀) stores.old stores.parts stores.roles
      (Gather.reaching stores.rotor) ((entry₀).venueWord (v₀) stores.parts stores.active stores.hubs stores.rotor stores.width)
      stores.names stores.ranks col low)
  have tables : stores.books = decoded := funext fun col=>funext (stores.registered col)
  let fieldWord (values : Val₀ (v₀).reference.nameBits (v₀).reference.countBits) : Word w :=
    ((DescentSIMDLookup.data ((stockWithBooks stores values).output x) l).val : Word w)
  change counted j = fieldWord stores.books
  exact (show counted j = fieldWord decoded from published x l).trans (congrArg fieldWord tables.symm)

include before tail cut in
/-- The original calendar pays for the primitive program on this cut and its entire output archive. -/
theorem cut_primitive_purchased {t reset τ β copies driftR degreeMax : ℕ}
    (grant : ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (cost : OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule : S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies tailBits)
    (depth : k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (frozen : tailBits=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (dr : drift+1≤ scale (Nat.log 2 payload/(2*β)) driftR) (degreeRoom : degree≤degreeMax)
    (grain : p≤payload) (seed : S.firstWidth G.b p≤payload) (hp : 0<p)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (slots : DatePorts.ArgumentSlots G S ports drift) (low : headerBase<root) :
    (L₀).Published (cut_primitive_stock stores) (DatePorts.ordinary (v₀) floor₀).archive.roles.bank final:=by
  have width : (v₀).primitiveRoof ((v₀).operandEnd floor₀)≤(v₀).fullEnd root:=by
    change (v₀).primitiveEnd floor₀≤(v₀).returnedEnd floor₀
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have budget:=registered_primitive_purchase X G S br ticket before tail cut op tailBits drift degree payload seats
    ports.venue.lanes ports ports.io.roster ordinary floor₀ grant cost schedule depth frozen dr degreeRoom
    grain seed hp archive slots
  have paid:=registered_primitive_rooms (radix:=radix) (X:=X) (G:=G) (S:=S) (ticket:=ticket) (op:=op) (frozen:=tailBits)
    (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (hostLanes:=ports.venue.lanes)
    (ports:=ports) (old:=ports.io.roster) (ordinary:=ordinary) (stageFloor:=floor₀) ticket.hubRows.choose
    (Nat.le_max_left ..) stores.entryFits budget.1 (width.trans_lt exec.limit)
  exact cut_primitive_published (before:=before) (tail:=tail) (cut:=cut) stores ticket.hubRows.choose low paid.1 paid.2

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
