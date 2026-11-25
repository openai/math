import OAI.Hierarchy.DescentCutRegisteredHeaderPrefix
import OAI.Hierarchy.DescentCutStoredRole
import OAI.Hierarchy.DescentCutNumericHeaderBounds
import OAI.Hierarchy.DescentCutSharedStampBound
import OAI.Hierarchy.DescentCutBirthDigits
import OAI.Hierarchy.DescentRegisteredChosenPointerSites
import OAI.Hierarchy.DescentRegisteredBookAxisJobs

namespace OAI
/-! The selected cable, pin and hidden-word keys on the original chronological cut. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedPriorOperand DescentDatedOperandReadPipeline DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedOperand DescentOperandVectorArena DescentHaloWalkRAM
open DescentRawCablePanel ProtocolRAM ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSixParty.SeedNamed.Branch DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (shape:v.VectorShape)
set_option hygiene false in
local notation "L" => v.resolver
set_option hygiene false in
local notation "A" => v.vector
set_option hygiene false in
local notation "ref" => v.reference
set_option hygiene false in
local notation "fmt" => v.ticket.depotShape v.short
set_option hygiene false in
local notation "E" => v.material
set_option hygiene false in
local notation "B" => v.bornBook
variable (floor:ℕ) (entry:v.ArgumentEntry) (mat:entry.Match v floor)
    (homes:(B).hosts=(A).hosts) (gs:(B).groups=(A).groups*(A).radix) (bits:(B).bits=(L).size+2)
    (pg:Fin (A).pageCount) (chip:Fin (B).hosts→Fin (B).groups→Cell (B).chipBits)
    (blocks:(L).blocks=(E).blocks) (bound:(L).hosts≤(E).hosts) (groups:(L).groups=(E).groups)
    (roster:Fin (E).oldHosts→Fin (fmt).degree→Option (Fin (E).oldHosts))
    {nb mb c:ℕ}
set_option hygiene false in
local notation "Rows" cap:arg bits_:arg => References.Rows A (ref).degree (ref).k (ref).oldNodes cap ((L).size+2) bits_ mb
variable (old:Rows c nb) (raw:Rows (ref).capacity nb)
set_option hygiene false in
local notation "previous" rows:arg => v.returnedBook shape rows
set_option hygiene false in
local notation "priorWords" rows:arg => fun j f h k=>booksHeader (previous rows) j h k f
set_option hygiene false in
local notation "mouths" rows:arg => fun j f h k=>take (((L).index.symm j).2.1)
  (v.mouthHeaderValue floor entry mat shape (v.headerMouthRows floor entry mat rows homes gs bits) chip homes gs j f h k)
variable (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
variable (bands : v.material.oldGroups = v.material.groups * v.material.blocks)
  (serial peer : Fin v.material.blocks →
    Fin (breadth (v.ticket.depotShape v.short).degree * DepotRAM.Material.roles (v.ticket.depotShape v.short)) →
    Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits)
local notation "wide" => v.wideMaterialValues roster state bands serial peer
set_option hygiene false in
local notation "heads" prev:arg rod:arg => v.originalValues (v.sampleHeads blocks bound groups
  (v.originHeaderValue shape ((rod) pg)) (priorWords prev) (mouths rod) wide (v.narrowValue roster))
set_option hygiene false in
local notation "words" prev:arg rod:arg => ticketAt v.ticketReadGeometry (SortedInput.values v.ticketReadGeometry
  (heads prev rod) (v.walkValues (Gather.reaching roster)))
set_option hygiene false in
local notation "route" prev:arg rod:arg => v.ticketRoles (words prev rod)
set_option hygiene false in
local notation "room" prev:arg rod:arg => ∀j h y,11*((route prev rod) j 1 h y).val+((route prev rod) j 2 h y).val<2^((L).size+2)
private def RegisteredRoleRoom := room raw raw

private theorem role_room_from_shared_pages
    (stamps : ∀(other : Fin (A).pageCount) (q : Fin (A).lows) (n : Fin (L).nodes)
        (h : Fin (A).hosts) (g : Fin ((A).groups*(A).radix)),
      HeaderWords.stamp (raw other q) v.originBits (L).nodes n h g =
      HeaderWords.stamp (raw pg q) v.originBits (L).nodes n h g)
    (base : 22*(fmt).cap+10 < 2^((L).size+2)) :
    RegisteredRoleRoom v shape floor entry mat homes gs bits pg chip blocks bound groups roster raw state bands serial peer := by
  intro j h y
  exact v.matched_role_room roster state bands serial peer blocks bound groups (v.originHeaderValue shape (raw pg))
    (priorWords raw) (mouths raw) j h y
    (v.raw_role_room_of_stamps floor entry mat shape pg raw chip homes gs bits stamps j h y) base

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open scoped Classical Fin.CommRing
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
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

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "pitch₀" => (2^(k+1)-1)*shelf
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "roleWidth" => (pop₀).roleBits
local notation "nb" => (v₀).reference.nameBits
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S («f»:=f) («g»:=g) («p»:=p) («radix»:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "peer_" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))
open DescentOrdinaryOriginMask
variable {w shelfHeader headerBase pos code exec}

local notation "axes" => selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
local notation "tall" => (entry₀).clip.core.values stores.parts stores.active
local notation "compact" => Fin (Fintype.card prior.V)
local notation "tickets" => fun x j (hostIndex:compact) groupIndex=>tall x j (hostIndex.castLE stores.oldFit) groupIndex
local notation "counts" => fun x (hostIndex:compact) groupIndex=>DescentOrdinaryAtomFieldRAM.RoleCounts.count mb
   ((entry₀).roleValues (v₀) stores.roles x (hostIndex.castLE stores.oldFit) groupIndex)
local notation "col" j:arg f:arg => (DescentOperandStateBanks.page ((f:Fin 4).castLE (by decide : 4≤7)) j)
local notation "V" => fun pg l=>onSourceAxes (axes).1 (axes).2.2 id (stores.books pg l)

open DescentLocalArchiveOrder DescentKernelHistory DescentBundleHistory DescentDatedPriorOperand
open DescentPackedOperand DescentPrimitivePalette DescentRetainedRangeDigits DescentHistoryOrder
local notation "issued₀" => issued_return_fields X G S br ticket before tail cut books₀ tailBits payload seats ports.venue.lanes ports.io.roster ordinary
local notation "fixed₀" => (DatePorts.ordinary_registered_signed ports ticket op g tailBits p f drift degree payload seats root ordinary (issued₀).2.2.2).1
private theorem verifiedEntryMatch {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
    (entry : old.ArgumentEntry) (same : new = old) {start : ℕ} (proof : entry.Match old start) :
    (entry.samePorts new).Match new start := by
  subst new
  cases entry
  exact proof
/-- The signed pass retains the seven physical fields of the original operand entry. -/
def cutSignedEntry : (phys₀).ArgumentEntry :=
  (entry₀).samePorts (phys₀)
local notation "ae" => cutSignedEntry (g:=g) (p:=p) (f:=f) (ports:=ports) (ticket:=ticket) (op:=op) (tailBits:=tailBits) (drift:=drift)
   (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
include before tail cut in
theorem cut_signed_match : (ae).Match phys₀ floor₀:=by
  exact verifiedEntryMatch (entry₀) (fixed₀) (mat₀)
include before tail cut in
theorem cut_signed_shape : (phys₀).VectorShape:=by
  exact (congrArg PhysicalOrdinary.VectorShape (fixed₀)).mpr (sh₀)
local notation "mt" => cut_signed_match (g:=g) (p:=p) (f:=f) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
  (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits)
  (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
local notation "vs" => cut_signed_shape (g:=g) (p:=p) (f:=f) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
  (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits)
  (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
local notation "U" => fun pg l=>onSourceAxes rfl (axes).2.2 id (stores.books pg l)
local notation "chip" => (entry₀).nativeChips (v₀) stores.inputs.toBirthShape stores.parts
local notation "E" => (phys₀).material
local notation "fmt" => (v₀).ticket.depotShape (v₀).short
local notation "L" => (phys₀).resolver
local notation "R₀" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster A ((prior.vertex.trans (Fin.castLEEmb stores.oldFit)).trans Fin.valEmbedding))

variable (canon:stores.Canonical) (arch:Archive W) (places:DatePorts.RangeRoom ports prior arch.bit)
    (enough:Fintype.card prior.V≤ports.operandHosts) (age:i<S.length)
    (width:(L).size+2=ports.operandBits)
    (bound:(L).hosts≤(E).hosts) (regGroups:(L).groups=(E).groups)
    (bands:S.groupCount i=(E).groups*(E).blocks) (stepFit:(phys₀).materialPitch=pitch₀)
    (blockFit:(E).blocks=2^k) (wide:Fintype.card next.V≤(phys₀).signed.hosts)
local notation "homes" => (dims₀ age radix).2.1
local notation "seedGroups" => stores.groups
local notation "prev" j:arg f:arg => DatePorts.physicalHeaderSource ports prior arch.bit places enough (wired original) j f
local notation "birth" j:arg f:arg => header_birth_at X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary stores width j f

include canon in
/-- Casting the already acquired board along its proved roster equality preserves all
of its material, including the selected matcher and the signed rows. -/
def CutStores.headerBoard : (v₀).SelectedBoard stores.oldFit R₀ stores.pick (donors original) (steps₀).parts :=
  canon.1 ▸ stores.board

local notation "B₀" => CutStores.headerBoard (stores:=stores) (canon:=canon)
local notation "symmetric" => registered_symmetric (v₀) stores.oldFit
local notation "serial" picked:arg agree:arg b:arg => (v₀).retainedSerial stores.oldFit R₀ picked (donors original) (steps₀).parts b agree wide age radix bands symmetric
local notation "peer" picked:arg agree:arg b:arg => (v₀).retainedPeer stores.oldFit R₀ picked (donors original) (steps₀).parts b agree wide age radix bands symmetric
local notation "signed" picked:arg agree:arg b:arg => (phys₀).wideMaterialValues R₀ (b).material bands (serial picked agree b) (peer picked agree b)
local notation "oldBook" rows:arg => (phys₀).returnedBook vs rows
local notation "ports₃" rows:arg => fun jobIndex fieldIndex hostIndex groupIndex=>take (((L).index.symm jobIndex).2.1)
   ((phys₀).mouthHeaderValue floor₀ ae mt vs
     ((phys₀).headerMouthRows floor₀ ae mt rows homes seedGroups rfl) chip homes seedGroups jobIndex fieldIndex hostIndex groupIndex)
local notation "heads" picked:arg agree:arg board:arg old:arg orig:arg => (phys₀).originalValues
  ((phys₀).sampleHeads code.blocks bound regGroups ((phys₀).originHeaderValue vs ((orig) page₀))
    (fun jobIndex fieldIndex hostIndex groupIndex=>booksHeader (oldBook old) jobIndex hostIndex groupIndex fieldIndex) (ports₃ orig)
    (signed picked agree board) ((phys₀).narrowValue R₀))
local notation "words" picked:arg agree:arg board:arg old:arg orig:arg => ticketAt (phys₀).ticketReadGeometry
  (SortedInput.values (phys₀).ticketReadGeometry (heads picked agree board old orig) ((phys₀).walkValues (Gather.reaching R₀)))
local notation "roles" picked:arg agree:arg board:arg old:arg orig:arg => (phys₀).ticketRoles (words picked agree board old orig)
local notation "NamesFit" picked:arg agree:arg b:arg old:arg orig:arg => ∀jobIndex hostIndex groupIndex,
  11*((roles picked agree b old orig) jobIndex 1 hostIndex groupIndex).val+((roles picked agree b old orig) jobIndex 2 hostIndex groupIndex).val<2^((L).size+2)
local notation "source" picked:arg agree:arg board:arg src:arg src₀:arg fits:arg => decodedBooks (oldBook src)
  (fun jobIndex hostIndex groupIndex=>DescentDatedPublicGrain.withGrain (phys₀).chosenGrain
    ((phys₀).ticketSides (words picked agree board src src₀) jobIndex hostIndex groupIndex)) (roles picked agree board src src₀) fits
local notation "chosenRoleRoom" picked:arg agree:arg chosenBoard:arg => PhysicalOrdinary.RegisteredRoleRoom
    (phys₀) vs floor₀ ae mt homes seedGroups rfl page₀ chip code.blocks bound regGroups R₀ stores.books
    (chosenBoard).material bands (serial picked agree chosenBoard) (peer picked agree chosenBoard)

private theorem equalStampsFromRows {D k K c H groups a nb' mb' : ℕ}
    (left right : DescentOrdinaryAtomFieldRAM.ScalarOperand.Values D k K c H groups a nb' mb')
    (bits₁ nodes : ℕ) (node : Fin nodes) (host : Fin H) (group : Fin groups) {common : Cell (bits₁*nodes)}
    (hl : selection _ nodes bits₁ (marked left host group) = common)
    (hr : selection _ nodes bits₁ (marked right host group) = common) :
    PhysicalOrdinary.HeaderWords.stamp left bits₁ nodes node host group =
    PhysicalOrdinary.HeaderWords.stamp right bits₁ nodes node host group :=
  congrArg (fun z => ((encode bits₁ nodes).symm z node).val) (hl.trans hr.symm)

include before tail cut canon age in
private theorem actualCutSharesStamps
    (other : Fin (vx₀).pageCount) (l : Fin (vx₀).lows) (n₀ : Fin (L).nodes)
    (h₀ : Fin (vx₀).hosts) (groupIdx : Fin ((vx₀).groups*(vx₀).radix)) :
    PhysicalOrdinary.HeaderWords.stamp (stores.books other l) (phys₀).originBits (L).nodes n₀ h₀ groupIdx =
      PhysicalOrdinary.HeaderWords.stamp (stores.books page₀ l) (phys₀).originBits (L).nodes n₀ h₀ groupIdx := by
  have measured := cut_stamp_row X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec stores age canon
  exact equalStampsFromRows (stores.books other l) (stores.books page₀ l) (v₀).originBits (L).nodes
    n₀ h₀ groupIdx (measured other l h₀ groupIdx) (measured page₀ l h₀ groupIdx)


include before tail cut canon in
/-- The complete routed role key fits on every physical lane of the selected board. -/
theorem cut_role_name_room (growth : 0<S.capGain) :
    PhysicalOrdinary.RegisteredRoleRoom (phys₀) vs floor₀ ae mt homes seedGroups rfl page₀ chip
      code.blocks bound regGroups R₀ stores.books (B₀).material bands (serial stores.pick stores.selected B₀) (peer stores.pick stores.selected B₀) := by
  apply PhysicalOrdinary.role_room_from_shared_pages
  · exact actualCutSharesStamps (stores:=stores) (canon:=canon) (age:=age) (before:=before) (tail:=tail) (cut:=cut)
  · exact DatePorts.registered_ticket_ordinal_room ports ticket op g tailBits p f drift degree payload seats root ordinary growth age

variable {stretch arity:ℕ} (hp:0<p) (one:1≤ stretch) (pin:∀x,p∣(bits x))
    (shape:WorldShape p stretch arch.bit) (step:p∣T.z) (number:Local arch.bit)
    (pinCode:P→ℕ) (labels:NodeOrder.All arch.bit→Label G s (S.grainAt G.b p 0) op)
    (flags:Fin (2^ports.venue.k)→Fin ports.nodes→Fin ports.operandHosts→Fin ports.venue.groups→ℕ)
local notation "shape₁" => afterOrdinary hp one pin ticket arch shape step
local notation "expected" => Reached.argumentPointer prior arch.bit number shape hp pinCode arity
variable (earlier:ports.ArchiveRead prior arch.bit number places shape op labels expected flags (wired original))
    (paid:∀vertex inputIndex,((shape.sites vertex).recipe hp).arity inputIndex≤ports.argumentsPerNode)
    (precision:2≤ports.operandBits) (packed:ports.operandBits*ports.nodes*ports.operandLanes≤w)
    (arityFit:∀vertex inputIndex,((shape.sites vertex).recipe hp).arity inputIndex≤arity)
    (countWide:ports.nodes<2^mb)
    (issued:∀x hostIndex groupIndex,(stores.roles x hostIndex groupIndex).val=(encode (printedBits G s (S.grainAt G.b p 0) op) ports.nodes (fun j=>
      (DatePorts.slotAt ports prior arch.bit number places (x.cast (congrArg (2^·) places.radix)) j hostIndex (groupIndex.cast places.groups)).elim 0
        (fun y=>token G s (S.grainAt G.b p 0) op (labels y)))).val)
    (rankRoom:breadth (A).degree*2^k≤2^((L).size+2)) (nameFit:11*(A).cap≤2^((L).size+2))
    (argumentsFit:(L).operands≤2^((L).size+2)) (mouthSize:11≤2^(bn₀).bits)
    (wireFit:next.placement.cap≤2^(phys₀).signed.fieldBits) (peerFit:next.placement.degree≤2^(phys₀).signed.fieldBits)
    (wireWide:next.placement.cap≤2^((L).size+2)) (peerWide:next.placement.degree≤2^((L).size+2))
    (cutRead:(phys₀).chosenGrain.val=(A).stage.z/p)


namespace StoredPointerFrame
open DescentSortedHaloRaster DescentPaidResidentCount DescentGL DescentScalarBookReshape
open scoped Classical Fin.CommRing
local notation "rrData" j:arg fI:arg => rangeValues ticket arch tickets age radix counts (prev j fI) (birth j fI)
local notation "rdAt" j:arg fI:arg => Values.transport (axes).2.1 (rfl : (vx₀).groups = S.groupCount (i+1))
  (rfl : (vx₀).radix = 2^k) width (rrData j fI)
local notation "mouthRd" j:arg => Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
  (rfl : (vx₀).groups = S.groupCount (i+1)) (rfl : (vx₀).radix = 2^k) width (rrData j (0 : Fin 4))
local notation "signedPage" j:arg fI:arg => (col j fI).cast (congrArg (7*·) (vs).operands)



private theorem verifiedSignedCutBlocks {K I : Type} [Field K] (v : PhysicalOrdinary K I)
    (blocks : v.resolver.blocks = v.material.blocks) :
    v.withIssuedSigned.resolver.blocks = v.withIssuedSigned.material.blocks := blocks

open Lean Meta Elab Term in
local elab "registeredCutJobs%[" xs:term,* "]" : term => do
  let rawArgs ← xs.getElems.mapM fun stx => elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  let args ← rawArgs.mapM instantiateMVars
  let fitDecl ← mkConstWithFreshMVarLevels ``PhysicalOrdinary.registered_axis_fit
  let jobsDecl ← mkConstWithFreshMVarLevels ``PhysicalOrdinary.registered_axis_jobs
  let fit := mkAppN fitDecl args
  let jobs := mkAppN jobsDecl args
  forallBoundedTelescope (← inferType fit) (some 1) fun boundNames _ => do
    let names := mkAppN fit boundNames
    let equalJobs := mkApp (mkAppN jobs boundNames) names
    let both ← mkAppM ``And.intro #[names, equalJobs]
    instantiateMVars (← mkLambdaFVars boundNames both)

private theorem selectedOperandPageCast {a b : ℕ} (align : a = b) (j : Fin a) (fieldNo : Fin 7) :
    (DescentOperandStateBanks.page fieldNo j).cast (congrArg (7*·) align) =
      DescentOperandStateBanks.page fieldNo (j.cast align) := by
  cases align
  rfl


private def takeInput {α : Sort _} (_ : α) (pr : Prop) : Prop := pr

def actualCutPointerClaim (picked:((A).stage.result nonneg).Choice) (agree:HEq picked choice)
    (board:(v₀).SelectedBoard stores.oldFit R₀ picked (donors original) (steps₀).parts)
    (nameRoom:chosenRoleRoom picked agree board) : Prop :=
  takeInput earlier <|
  takeInput paid <|
  takeInput precision <|
  takeInput packed <|
  takeInput arityFit <|
  takeInput countWide <|
  takeInput issued <|
  takeInput rankRoom <|
  takeInput nameFit <|
  takeInput argumentsFit <|
  takeInput mouthSize <|
  takeInput wireFit <|
  takeInput peerFit <|
  takeInput wireWide <|
  takeInput peerWide <|
  takeInput cutRead <|
  takeInput stepFit <|
  takeInput blockFit <|
  takeInput canon <|
  takeInput enough <|
  takeInput width <|
  Reached.PointerSites next (phys₀) (ticket.advance arch).bit (advance ticket arch number) (shape₁) hp pinCode
      (source picked agree board stores.books stores.books nameRoom)

open Lean Meta Elab Command
set_option maxRecDepth 24000 in
run_cmd liftTermElabM do
  let ci ← getConstInfo ``actualCutPointerClaim
  forallTelescope ci.type fun xs _ => do
    let some beforeCut ← xs.findIdxM? (fun x => do return (← x.fvarId!.getDecl).userName == `ticket) | throwError "missing ticket"
    let cutoff := beforeCut + 1
    let early := xs.extract 0 cutoff
    let later := xs.extract cutoff xs.size
    let terminal := mkAppN (.const ci.name (ci.levelParams.map .param)) xs
    let val ← mkLambdaFVars early (← mkForallFVars later terminal)
    addDecl <| .defnDecl {
      name := ci.name.getPrefix ++ `actualCutFrameObligation
      levelParams := ci.levelParams
      type := ← inferType val
      value := val
      hints := .regular 0
      safety := .safe }


attribute [local irreducible] actualCutFrameObligation actualCutPointerClaim

set_option maxHeartbeats 3500000 in
theorem stored_sites_through_original_frame : @actualCutFrameObligation F (inferInstance : Field F) cp pins X G S k
    n h C f g p R he
    hu radix run c br W i z
    D z' D' rate prior T nonneg choice
    norm next ticket := by
  have rateFits := ticket.sourceRate
  subst rate
  have stageFits := eq_of_heq ticket.placement
  subst T
  unfold actualCutFrameObligation
  intro «before» «tail» «cut» «ports» «op» «tailBits» «drift» «degree»
    «payload» «seats» «root» «ordinary» «w» «shelfHeader» «headerBase» «pos»
    «code» «exec» «original» «stores» «canon» «arch»
    «places» «enough» «age» «width» «bound» «regGroups» «bands» «stepFit»
    «blockFit» «wide» «stretch» «arity» «hp» «one» «pin» «shape»
    «step» «number» «pinCode» «labels» «flags» «earlier» «paid» «precision»
    «packed» «arityFit» «countWide» «issued» «rankRoom» «nameFit» «argumentsFit» «mouthSize»
    «wireFit» «peerFit» «wireWide» «peerWide» «cutRead» «picked» «agree»
  have sameChoice : picked = choice := eq_of_heq agree
  subst picked
  intro «board» «nameRoom»
  unfold actualCutPointerClaim
  simp only [takeInput]
  have ticketAtChoice:(v₀).atSelected choice HEq.rfl=⟨norm,next,ticket,HEq.rfl,HEq.rfl,HEq.rfl⟩:=by
    generalize (v₀).atSelected choice HEq.rfl=a
    rcases a with ⟨n,r,t,en,er,et⟩
    have hn : n = norm := eq_of_heq en
    subst n
    have hr : r = next := eq_of_heq er
    subst r
    have ht : t = ticket := eq_of_heq et
    subst t
    rfl
  let jobEquality := (registeredCutJobs%[F, (P), (inferInstance : Field F), (phys₀), vs, floor₀, ae, mt, homes, seedGroups, (Eq.refl (phys₀).bornBook.bits), page₀, chip, (verifiedSignedCutBlocks (v₀) code.blocks), bound, regGroups, (signed choice HEq.rfl board), R₀, nb, mb, stores.books, trueCap, (Packed.bits pitch₀), (axes).1, (axes).2.2]) nameRoom
  let names := jobEquality.1
  have same := jobEquality.2
  refine (congrArg (fun jobs => Reached.PointerSites next (phys₀) (ticket.advance arch).bit (advance ticket arch number) (shape₁) hp pinCode jobs) same).mp ?_
  have active := cut_stored_counts X G S ticket ports op tailBits drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec stores arch.bit number places labels issued countWide
  let old₀:=fun blockIndex hostIndex groupIndex=>((prev 0 (0:Fin 4)) blockIndex hostIndex groupIndex).cast (congrArg (fun n:ℕ=>2^(n*ports.nodes)) width.symm)
  let born₀:=fun blockIndex t argIndex hostIndex groupIndex=>((birth 0 (0:Fin 4)) blockIndex t argIndex hostIndex groupIndex).cast (congrArg (2^·) width.symm)
  let bornAt:=fun argIndex fieldIndex=>birth argIndex fieldIndex
  let framePrefix := fun frame : PhysicalOrdinary.AtSelected (v₀) choice =>
    ∀ l : Fin (vx₀).lows, Values.Prefix stores.oldFit
      (Values.originTransport rfl rfl rfl (axes).1 (axes).2.1
        (rfl:(vx₀).groups=S.groupCount (i+1)) (rfl:(vx₀).radix=2^k) rfl
        (rangeValues frame.link arch tickets age radix counts old₀ born₀) l)
      (onSourceAxes rfl (axes).2.2 id (stores.books page₀ l))
  have stampedAtChosenTicket : framePrefix ((v₀).atSelected choice HEq.rfl) := by
    apply Eq.mpr (congrArg framePrefix ticketAtChoice)
    exact cut_header_stamp_prefix X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary stores arch places enough age width canon precision packed
  have bind:=PaddedOrigin.registered_chosen_sites («v»:=v₀) («oldFit»:=stores.oldFit) («selected»:=choice)
    («choiceEq»:=HEq.rfl) («arch»:=arch) («m»:=donors original) («parts»:=(steps₀).parts) («B»:=board)
    («tokens»:=tickets) («age»:=age) («radix»:=radix) («hp»:=hp) («one»:=one) («pin»:=pin)
    («sh»:=shape) («unit»:=step) («ports»:=ports) («mem»:=wired original) («room»:=places) («population»:=enough)
    («prior»:=number) («counts»:=counts) («live»:=active.1) («empty»:=active.2) («pinCode»:=pinCode)
    («arity»:=arity) («op»:=op) («labels»:=labels) («flags»:=flags) («stored»:=earlier)
    («paid»:=paid) («bitsFit»:=packed) («birthAt»:=bornAt) («shape»:=vs) («lo»:=(axes).2.1)
    («gs»:=rfl) («rad»:=rfl) («field»:=width) («hostFit»:=stores.oldFit) («V»:=V)
    («refD»:=rfl) («refK»:=rfl) («refN»:=rfl) («refC»:=(axes).1) («bl»:=code.blocks)
    («hb»:=bound) («mg»:=regGroups) («bands»:=bands) («stepFit»:=stepFit) («blockFit»:=blockFit)
    («origPrevious»:=old₀) («origBorn»:=born₀) («large»:=(U) page₀)
    («prefix»:=stampedAtChosenTicket) («wide»:=wide) («floor»:=floor₀) («entry»:=ae) («mat»:=mt) («homes»:=homes)
    («groups»:=seedGroups) («bits_»:=rfl) («U»:=U) («chip»:=chip) («nameRoom»:=names)
  let rr := BitDescription.scannedRows nonneg (A).stage
  let ly := bestLayout (branchWidth G (fun _ : rr.pairs => (A).stage.z) (rr.profile choice))
  let groupsAt := GadgetNetwork.newSite W.graph rr.pick ly rr.pack
  let stockAt := fun frame : PhysicalOrdinary.AtSelected (v₀) choice =>
    Descriptors shelf k (A).pos (A).block (ticketParent (he:=nonneg) (T:=(A).stage))
      (ticketSlot (c:=choice) frame.link) (((activeChart frame.link).key nonneg (A).stage choice) ∘ groupsAt)
      prior.vertex (Function.Embedding.refl _) (rotor (A) (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding))) tickets
  have material : stockAt ((v₀).atSelected choice HEq.rfl) := by
    apply Eq.mpr (congrArg stockAt ticketAtChoice)
    exact (cut_authentic_material (stores:=stores) canon).1
  have provided := bind material
  dsimp only at provided
  have groupEq (oldGroup:Fin (S.groupCount i)) :
      (finProdFinEquiv ((S.groupDigits age radix) oldGroup)).cast
        (stores.groups.trans (congrArg₂ Nat.mul (rfl:(phys₀).vector.groups=S.groupCount (i+1))
          (rfl:(phys₀).vector.radix=2^k))).symm = oldGroup.cast stores.inputs.groups.symm :=
    cut_birth_group age radix (stores.groups.trans (congrArg₂ Nat.mul (rfl:(phys₀).vector.groups=S.groupCount (i+1))
      (rfl:(phys₀).vector.radix=2^k))) stores.inputs.groups oldGroup
  have trueFields := cut_birth_digits (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before)
    (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree)
    (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader)
    (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) (width:=width)
  let zero:Fin (vx₀).operands:=⟨0,code.slots⟩

  apply provided arityFit rankRoom nameFit argumentsFit
  · intro j fieldIndex l
    have colEq : signedPage j fieldIndex = col (j.cast (sh₀).operands) fieldIndex := by
      exact selectedOperandPageCast (vs).operands j _
    exact (congrArg (fun pg => Values.Prefix stores.oldFit ((rdAt j.val fieldIndex) l) ((V) pg l)) colEq).mpr
      (cut_header_prefix X G S br ticket before tail cut ports op tailBits drift degree payload seats root
      ordinary stores arch places enough age width (canon) precision packed
      (j.cast (sh₀).operands) fieldIndex l)
  · intro j l
    have pageEq : (phys₀).headerMouthPage floor₀ ae mt (j.cast ((vs).operands.trans (mt).newArgs.symm)) =
         col (j.cast (sh₀).operands) (0 : Fin 4) := by
      apply Fin.ext
      rfl
    rw [pageEq]
    exact cut_header_origin_prefix X G S br ticket before tail cut ports op tailBits drift degree payload seats root
      ordinary stores arch places enough age width (canon) precision packed
      (j.cast (sh₀).operands) 0 l
  · rfl
  · rfl
  · exact (selected_birth_shapes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary).2.2.2.2.2.2
  · exact mouthSize

  · intro pair
    erw [groupEq]
    with_unfolding_all exact (trueFields zero pair 0).1
  · intro pair a
    erw [groupEq]
    with_unfolding_all exact (trueFields zero pair 0).2.1 a
  · intro j pair party fieldIndex
    erw [groupEq]
    have h := (trueFields (j.cast (sh₀).operands) pair party).2.2 fieldIndex
    have scale := (selected_birth_shapes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary).2.2.2.2.2.2
    erw [scale] at h
    with_unfolding_all exact h


  · exact wireFit
  · exact peerFit
  · exact wireWide
  · exact peerWide
  · exact cutRead



end StoredPointerFrame

include before tail cut earlier paid precision packed arityFit countWide issued rankRoom nameFit argumentsFit
  mouthSize wireFit peerFit wireWide peerWide cutRead stepFit blockFit canon enough width in
private theorem stored_sites_for_choice (picked:((A).stage.result nonneg).Choice) (agree:HEq picked choice)
    (board:(v₀).SelectedBoard stores.oldFit R₀ picked (donors original) (steps₀).parts)
    (nameRoom:chosenRoleRoom picked agree board) :
    Reached.PointerSites next (phys₀) (ticket.advance arch).bit (advance ticket arch number) (shape₁) hp pinCode
      (source picked agree board stores.books stores.books nameRoom) := by
  exact @StoredPointerFrame.stored_sites_through_original_frame
    «F» (inferInstance : Field F) «cp» «pins» «X» «G» «S» «k» «n» «h»
    «C» «f» «g» «p» «R» «he» «hu» «radix» «run» «c»
    «br» «W» «i» «z» «D» «z'» «D'» «rate» «prior» «T»
    «nonneg» «choice» «norm» «next» «ticket» «before» «tail» «cut» «ports» «op»
    «tailBits» «drift» «degree» «payload» «seats» «root» «ordinary» «w» «shelfHeader» «headerBase»
    «pos» «code» «exec» «original» «stores» «canon» «arch» «places» «enough» «age»
    «width» «bound» «regGroups» «bands» «stepFit» «blockFit» «wide» «stretch» «arity» «hp»
    «one» «pin» «shape» «step» «number» «pinCode» «labels» «flags» «earlier» «paid»
    «precision» «packed» «arityFit» «countWide» «issued» «rankRoom» «nameFit» «argumentsFit» «mouthSize» «wireFit»
    «peerFit» «wireWide» «peerWide» «cutRead» «picked» «agree» «board» «nameRoom»

include before tail cut earlier paid precision packed arityFit countWide issued rankRoom nameFit argumentsFit
  mouthSize wireFit peerFit wireWide peerWide cutRead stepFit blockFit enough width in
/-- The archived source keys and both kinds of public arguments on the
actual signed, registered board and the earlier six W fields at this cut. -/
theorem cut_stored_pointer_sites
    (nameRoom:chosenRoleRoom stores.pick stores.selected B₀) :
    Reached.PointerSites next phys₀ (ticket.advance arch).bit (advance ticket arch number) shape₁ hp pinCode
      (source stores.pick stores.selected B₀ stores.books stores.books nameRoom):=by
  exact stored_sites_for_choice (one:=one) (pin:=pin) (step:=step) (ports:=ports) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (canon:=canon) (earlier:=earlier) (paid:=paid) (precision:=precision)
    (packed:=packed) (arityFit:=arityFit) (countWide:=countWide) (issued:=issued) (rankRoom:=rankRoom)
    (nameFit:=nameFit) (argumentsFit:=argumentsFit) (mouthSize:=mouthSize) (wireFit:=wireFit)
    (peerFit:=peerFit) (wireWide:=wireWide) (peerWide:=peerWide) (cutRead:=cutRead) (stepFit:=stepFit)
    (blockFit:=blockFit) (enough:=enough) (width:=width) (before:=before) (tail:=tail) (cut:=cut)
    (number:=number) (labels:=labels) (flags:=flags) (pinCode:=pinCode) (op:=op) (br:=br) (X:=X) (G:=G) (S:=S) (ticket:=ticket) (arch:=arch) (places:=places) (stores:=stores) (picked:=stores.pick)
    (agree:=stores.selected) (board:=B₀) (nameRoom:=nameRoom)

include before tail cut earlier paid precision packed arityFit countWide issued rankRoom nameFit argumentsFit
  mouthSize wireFit peerFit wireWide peerWide cutRead stepFit blockFit enough width in
set_option maxHeartbeats 12000000 in
/-- The literal decoded source with its all-row bound deduced from the acquired stamps. -/
theorem cut_acquired_pointer_sites (growth:0<S.capGain) :
    let room:=cut_role_name_room (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
      (before:=before) (tail:=tail) (cut:=cut) (stores:=stores) (canon:=canon)
      (age:=age) (bound:=bound) (regGroups:=regGroups) (bands:=bands) (wide:=wide) growth
    Reached.PointerSites next phys₀ (ticket.advance arch).bit (advance ticket arch number) shape₁ hp pinCode
      (source stores.pick stores.selected B₀ stores.books stores.books room):=by
  intro room
  exact cut_stored_pointer_sites (one:=one) (pin:=pin) (step:=step) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (canon:=canon) (earlier:=earlier) (paid:=paid)
    (precision:=precision) (packed:=packed) (arityFit:=arityFit) (countWide:=countWide)
    (issued:=issued) (rankRoom:=rankRoom) (nameFit:=nameFit) (argumentsFit:=argumentsFit)
    (mouthSize:=mouthSize) (wireFit:=wireFit) (peerFit:=peerFit) (wireWide:=wireWide)
    (peerWide:=peerWide) (cutRead:=cutRead) (stepFit:=stepFit) (blockFit:=blockFit)
    (enough:=enough) (width:=width) (before:=before) (tail:=tail) (cut:=cut)
    (X:=X) (G:=G) (S:=S) (br:=br) (stores:=stores) (ticket:=ticket) (nameRoom:=room)

set_option maxHeartbeats 6000000
include before tail cut earlier paid packed arityFit issued cutRead enough width in
/-- At the rounded physical width, the single old rectangle and the public halo span
suffice for all eight scalar bounds. -/
theorem cut_calibrated_pointer_sites (growth:0<S.capGain) (previous:ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (walks:breadth (maximumDegree (S.rounds+1))≤2^k) :
    let room:=cut_role_name_room (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
      (before:=before) (tail:=tail) (cut:=cut) (stores:=stores) (canon:=canon)
      (age:=age) (bound:=bound) (regGroups:=regGroups) (bands:=bands) (wide:=wide) growth
    Reached.PointerSites next phys₀ (ticket.advance arch).bit (advance ticket arch number) shape₁ hp pinCode
      (source stores.pick stores.selected B₀ stores.books stores.books room) :=by
  let scalarBounds := cut_numeric_header_bounds ports ticket op g tailBits p f drift degree payload seats root ordinary previous walks
  let countBounds := cut_numeric_counts ports ticket op g tailBits p f drift degree payload seats root ordinary width
  let materialAxes := cut_numeric_material_axes ports ticket op g tailBits p f drift degree payload seats root ordinary
  exact cut_acquired_pointer_sites (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
    (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits)
    (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
    (stores:=stores) (canon:=canon) (arch:=arch) (places:=places) (enough:=enough) (age:=age) (width:=width)
    (bound:=bound) (regGroups:=regGroups) (bands:=bands) (stepFit:=materialAxes.1) (blockFit:=materialAxes.2)
    (wide:=wide) (hp:=hp) (one:=one) (pin:=pin) (shape:=shape) (step:=step) (number:=number)
    (pinCode:=pinCode) (labels:=labels) (flags:=flags) (earlier:=earlier) (paid:=paid)
    (precision:=countBounds.1) (packed:=packed) (arityFit:=arityFit) (countWide:=countBounds.2) (issued:=issued)
    (rankRoom:=scalarBounds.1) (nameFit:=scalarBounds.2.1) (argumentsFit:=scalarBounds.2.2.1)
    (mouthSize:=scalarBounds.2.2.2.1) (wireFit:=scalarBounds.2.2.2.2.1) (peerFit:=scalarBounds.2.2.2.2.2.1)
    (wireWide:=scalarBounds.2.2.2.2.2.2.1) (peerWide:=scalarBounds.2.2.2.2.2.2.2) (cutRead:=cutRead) (growth:=growth)

include before tail cut earlier paid packed arityFit issued cutRead enough width canon in
/-- The very job whose normalized word is printed by this cut implements all
three kinds of true argument pointer. The stored window includes its padded lanes. -/
theorem cut_argument_pointer_sites (growth : 0<S.capGain)
    (previous : ports.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (walks : breadth (maximumDegree (S.rounds+1))≤2^k) :
    ∃ jobs : Fin (L).jobs→DescentDatedPriorOperand.Source L,
      (∀j, Reads (Banks.wordBank (v₀).resolver ((v₀).normalizedEnd floor₀) j)
        (fun h y=>DescentPackedOperand.word ((jobs j).compiled h y)) (v₀).resolver.lanes
        (DatePorts.ordinaryMetadata ports ticket op g tailBits p f drift degree payload seats root ordinary
          w shelfHeader headerBase pos code exec original)) ∧
      Reached.PointerSites next phys₀ (ticket.advance arch).bit (advance ticket arch number)
        shape₁ hp pinCode jobs := by
  have age : i < S.length := ticket.hubRows.choose
  let room:=cut_role_name_room (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
    (before:=before) (tail:=tail) (cut:=cut) (stores:=stores) (canon:=canon) (age:=age)
    (bound:=stores.hostBound) (regGroups:=stores.groupBound) (bands:=stores.groupSplit) (wide:=stores.nextFit) growth
  have sound:=cut_calibrated_pointer_sites (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket)
    (before:=before) (tail:=tail) (cut:=cut) (stores:=stores) (canon:=canon) (arch:=arch)
    (places:=places) (enough:=enough) (age:=age) (width:=width) (bound:=stores.hostBound)
    (regGroups:=stores.groupBound) (bands:=stores.groupSplit) (wide:=stores.nextFit)
    (hp:=hp) (one:=one) (pin:=pin) (shape:=shape) (step:=step) (number:=number)
    (pinCode:=pinCode) (labels:=labels) (flags:=flags) (earlier:=earlier) (paid:=paid)
    (packed:=packed) (arityFit:=arityFit) (issued:=issued) (cutRead:=cutRead) growth previous walks
  refine ⟨_, ?_, sound⟩
  exact stores.resolvedWords R₀ canon.1 age stores.nextFit stores.groupSplit symmetric
    stores.hostBound stores.groupBound mt vs room

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
