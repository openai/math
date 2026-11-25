import OAI.Hierarchy.ProofField
import OAI.Hierarchy.DescentNamedCutResolverMemory
import OAI.Hierarchy.DescentNamedCutVectorPages
import OAI.Hierarchy.DescentRegisteredOperandHeaderRoom
import OAI.Hierarchy.DescentNamedCutSignedShelf
import OAI.Hierarchy.DescentDatedOriginalTaggedHeads
import OAI.Hierarchy.DescentNamedRegisteredBoardVenue
import OAI.Hierarchy.DescentRegisteredTicketKeyRoom
import OAI.Hierarchy.DescentRegisteredSectionPopulation

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
noncomputable section
variable {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
variable (same : new = old) (entry : old.ArgumentEntry) {floor w : ℕ}
variable (m : entry.Match old floor) (m' : (entry.samePorts new).Match new floor)
variable (p : Fin (7*old.vector.operands)) (q : Fin (7*new.vector.operands)) (pq : HEq p q)

include same pq

private theorem selected_cut_header_room
    (h : old.OperandHeaderRoom floor entry m (entry.directory old floor m).refs ((entry.directory old floor m).refs p) w) :
    new.OperandHeaderRoom floor (entry.samePorts new) m'
      ((entry.samePorts new).directory new floor m').refs
      (((entry.samePorts new).directory new floor m').refs q) w := by
  subst new
  have sp : p = q := eq_of_heq pq
  subst q
  cases entry
  exact h

private theorem selected_cut_ticket_admission (c : old.SignedChart) (c' : new.SignedChart)
    (h : old.TicketAdmission floor w c entry m p) :
    new.TicketAdmission floor w c' (entry.samePorts new) m' q := by
  subst new
  have sp : p = q := eq_of_heq pq
  subst q
  cases entry
  exact h

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPackedColony DescentSIMDLookup
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
variable (same : new = old) (entry : old.ArgumentEntry) {floor w : ℕ}
include same in
private theorem selected_cut_chip_span (bound : old.bornBook.rows ≤ (entry.chipBank old floor).size) :
    new.bornBook.rows ≤ ((entry.samePorts new).chipBank new floor).size := by
  subst new
  cases entry
  exact bound
include same in
private theorem selected_cut_chip_read {oldMem newMem : Memory w} (memEq : newMem = oldMem)
    {oldChip : Fin old.bornBook.hosts → Fin old.bornBook.groups → Cell old.bornBook.chipBits}
    {newChip : Fin new.bornBook.hosts → Fin new.bornBook.groups → Cell new.bornBook.chipBits}
    (chipEq : HEq oldChip newChip)
    (read : Reads (entry.chipBank old floor) oldChip old.bornBook.lanes (entry.mountedTape old floor oldMem)) :
    Reads ((entry.samePorts new).chipBank new floor) newChip new.bornBook.lanes
      ((entry.samePorts new).mountedTape new floor newMem) := by
  subst new
  subst newMem
  obtain rfl := eq_of_heq chipEq
  cases entry
  exact read

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentDatedAddressBook DescentParallelBase.ParentFilter
open DescentDatedPriorOperand DescentPackedColony DescentDatedOperandReadPipeline DescentOperandVectorArena DescentOperandStateBanks
open DescentPackedZip DescentColonies DescentHistoryOrder DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option maxHeartbeats 400000
variable {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
variable {nb mb w floor : ℕ}
private abbrev CutBooks (v : PhysicalOrdinary K I) (digits count : ℕ) :=
  References.Rows v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity (v.resolver.size+2) digits count

private theorem selected_cut_mounted_pages (same : new=old) (entry : old.ArgumentEntry)
    (matched : entry.Match old floor) (newMatch : (entry.samePorts new).Match new floor)
    {oldBooks : CutBooks old nb mb} {newBooks : CutBooks new nb mb} (bookEq : HEq oldBooks newBooks)
    {source target : Memory w} (memory : source = target)
    (pages : ∀ p q, ScalarOperand.Measured (((entry.directory old floor matched).refs p) q) (oldBooks p q)
      old.resolver.nodes (old.vector.lanes*old.vector.radix) (old.vectorStart floor) (entry.mountedTape old floor source)) :
    ∀ p q, ScalarOperand.Measured ((((entry.samePorts new).directory new floor newMatch).refs p) q) (newBooks p q)
      new.resolver.nodes (new.vector.lanes*new.vector.radix) (new.vectorStart floor)
        ((entry.samePorts new).mountedTape new floor target) := by
  subst new
  subst target
  have books : oldBooks = newBooks := eq_of_heq bookEq
  subst newBooks
  cases entry
  exact pages

private theorem selected_cut_operand_book_tags (same : new=old) (shape : old.VectorShape) (newShape : new.VectorShape)
    {oldBooks : CutBooks old nb mb} {newBooks : CutBooks new nb mb} (bookEq : HEq oldBooks newBooks)
    (typed : BookTags (old.registeredOperandBooks shape oldBooks)) :
    BookTags (fun x p => previousValues new.resolver new.vector newShape.operands newShape.blocks
      newShape.hosts newShape.groups (References.returnedValue new.vector newBooks new.resolver.nodes) p x) := by
  subst new
  have books : oldBooks = newBooks := eq_of_heq bookEq
  subst newBooks
  exact typed


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

/-! All resolved physical operand words at a selected registered ordinary cut. -/
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

private theorem selectedMaterialBlocks {K I : Type} [Field K] (v : PhysicalOrdinary K I)
    (blocks : v.resolver.blocks = v.material.blocks) :
    v.withIssuedSigned.resolver.blocks = v.withIssuedSigned.material.blocks := blocks

/-- The numerical register file, the selected native board, and their source reads at the signed cut. -/
structure CutStores (original : Memory w) where
  old : Pages (entry₀).previous.operands → Fin (entry₀).previous.blocks → Fin (entry₀).previous.hosts →
    Fin (entry₀).previous.groups → Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous)
  roles : Fin (entry₀).previous.blocks → Fin (entry₀).previous.hosts → Fin G₀ →
    Cell ((pop₀).roleBits*(pop₀).nodes)
  active : Active
  hubs : Fin H₀ → Cell 1
  oldFit : Fintype.card prior.V ≤ (v₀).area.H
  rotor : Fin (v₀).area.H → Fin (A).degree → Option (Fin (v₀).area.H)
  pick : ((A).stage.result nonneg).Choice
  board : (v₀).SelectedBoard oldFit rotor pick (donors original) (steps₀).parts
  selected : HEq pick choice
  parts : Fin H₀ → Fin G₀ → DepotRAM.Parts (entry₀).clip.venue.socket
  material : parts=board.material
  actors : Reads (entry₀).venue.actors active (entry₀).clip.actorPitch (wired original)
  flags : ∀h : Fin H₀,(wired original) ((entry₀).venue.hub.base+h.val)=((hubs h).val:Word w)
  oldRead : ∀x pg,Reads (previousBank (entry₀).previous (entry₀).previousBase x pg)
    (old pg x) (entry₀).previous.lanes (wired original)
  roleRead : ∀x,Reads ((entry₀).role x) (roles x) (entry₀).rolePitch (wired original)
  panel : Reads (entry₀).venue.panel (fun h g=>DepotRAM.combine (entry₀).clip.venue.socket (parts h g))
    (entry₀).clip.panelPitch (wired original)
  peers : ∀h j,(wired original) ((entry₀).venue.adjacency.base+(h.val*(entry₀).clip.venue.socket.degree+j.val))=
    (number (rotor h j):Word w)
  inputs : (entry₀).InputShape (v₀)
  width : Packed.bits (entry₀).clip.venue.names*(entry₀).clip.actorCount=(v₀).reference.nameBits*(v₀).reference.actors
  names : (pop₀).nameBits=(v₀).reference.nameBits
  ranks : (pop₀).donors=(v₀).reference.donors
  groups : (v₀).bornBook.groups=(v₀).vector.groups*(v₀).vector.radix
  books : Val₀ (v₀).reference.nameBits (v₀).reference.countBits
  registered : ∀col low,books col low=groupValues groups ((entry₀).registeredValues (v₀) inputs
    floor₀ (mat₀) old parts roles (Gather.reaching rotor) ((entry₀).venueWord (v₀) parts active hubs rotor width)
    names ranks col low)

  entryFits : (entry₀).Room (v₀) floor₀ w
  oldPitch : 0<(entry₀).previous.lanes
  rolePitch : 0<(entry₀).rolePitch
  oldBanks : ∀x pg,(previousBank (entry₀).previous (entry₀).previousBase x pg).Fits w ((v₀).signedEnd floor₀)
  roleLo : ∀x,((entry₀).role x).base+((entry₀).role x).size≤(v₀).signedEnd floor₀
  roleRoom : ∀x,(entry₀).previous.hosts*chunks G₀ (entry₀).rolePitch≤((entry₀).role x).size
  actorsPositive : 0<(entry₀).clip.actorPitch
  admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀
  previousGroups : ports.venue.groups=S.groupCount i
  primitiveHosts : (v₀).paletteShape.hosts=(v₀).bornBook.hosts
  hostBound : (phys₀).resolver.hosts≤(phys₀).material.hosts
  groupBound : (phys₀).resolver.groups=(phys₀).material.groups
  groupSplit : S.groupCount i=(phys₀).material.groups*(phys₀).material.blocks
  nextFit : Fintype.card next.V≤(phys₀).signed.hosts
  /-- The scalar job assembled from the two native stages of this board is the
  word actually read at the metadata writer. The equality allows a consumer to
  use the original host-order presentation of the acquired rotor. -/
  resolvedWords : ∀(r : Fin (v₀).area.H→Fin (A).degree→Option (Fin (v₀).area.H))
    (same : rotor=r) (age : i<S.length) (wide : Fintype.card next.V≤(phys₀).signed.hosts)
    (bands : S.groupCount i=(phys₀).material.groups*(phys₀).material.blocks)
    (reciprocal : ∀a b j,r a j=some b→∃l,r b l=some a)
    (bound : (phys₀).resolver.hosts≤(phys₀).material.hosts)
    (groupEq : (phys₀).resolver.groups=(phys₀).material.groups)
    (mt : ((entry₀).samePorts (phys₀)).Match (phys₀) floor₀) (shape : (phys₀).VectorShape),
    let b : (v₀).SelectedBoard oldFit r pick (donors original) (steps₀).parts:=same ▸ board
    let serial:=(v₀).retainedSerial oldFit r pick (donors original) (steps₀).parts b selected wide age radix bands reciprocal
    let peer:=(v₀).retainedPeer oldFit r pick (donors original) (steps₀).parts b selected wide age radix bands reciprocal
    let ae:=(entry₀).samePorts (phys₀)
    let old:=fun j f h g=>ScalarOperand.take (((phys₀).resolver.index.symm j).2.1)
      ((phys₀).previousHeaderValue shape books j f h g)
    let home:=(dims₀ age radix).2.1
    let born:=fun j f h g=>ScalarOperand.take (((phys₀).resolver.index.symm j).2.1)
      ((phys₀).mouthHeaderValue floor₀ ae mt shape ((phys₀).headerMouthRows floor₀ ae mt books home groups rfl)
        ((entry₀).nativeChips (v₀) inputs.toBirthShape parts) home groups j f h g)
    let heads:=(phys₀).sampleHeads (selectedMaterialBlocks (v₀) code.blocks) bound groupEq ((phys₀).originHeaderValue shape (books page₀)) old born
      ((phys₀).wideMaterialValues r b.material bands serial peer) ((phys₀).narrowValue r)
    let val:=ticketAt (phys₀).ticketReadGeometry (SortedInput.values (phys₀).ticketReadGeometry
      ((phys₀).originalValues heads) ((phys₀).walkValues (Gather.reaching r)))
    let roles:=(phys₀).ticketRoles val
    ∀(room : ∀j h g,11*(roles j 1 h g).val+(roles j 2 h g).val<2^((phys₀).resolver.size+2)),
    let prev:=fun x pg=>previousValues (phys₀).resolver (phys₀).vector shape.operands shape.blocks shape.hosts shape.groups
      (References.returnedValue (phys₀).vector books (phys₀).resolver.nodes) pg x
    let jobs:=decodedBooks prev (fun j h g=>DescentDatedPublicGrain.withGrain (phys₀).chosenGrain
      ((phys₀).ticketSides val j h g)) roles room
    ∀j,Reads (Banks.wordBank (v₀).resolver ((v₀).normalizedEnd floor₀) j)
      (fun h g=>DescentPackedOperand.word ((jobs j).compiled h g)) (v₀).resolver.lanes
      (DatePorts.ordinaryMetadata ports ticket op g tailBits p f drift degree payload seats root ordinary
        w shelfHeader headerBase pos code exec original)


section
variable {X G S ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec}

/-- The numerical neighbor table, live actor masks, and hub bits use the earlier stage's host order. -/
def CutStores.Canonical {original : Memory w}
    (held : CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original) : Prop :=
  let hosts:=prior.vertex.trans (Fin.castLEEmb held.oldFit)
  held.rotor=hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding)) ∧
    held.active=Prepare.actors A (Function.Embedding.refl _) hosts ∧ held.hubs=Census.hub A hosts

end

private theorem selectedEntryMatch {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
    (entry : old.ArgumentEntry) (same : new = old) {start : ℕ} (proof : entry.Match old start) :
    (entry.samePorts new).Match new start := by
  subst new
  cases entry
  exact proof

private theorem receiptRoomAt {α : Type*} {old new : α} {a b d e : ℕ}
    (Q : α → ℕ → ℕ → Prop) (model : new = old) (start : a = b) (degree : d = e)
    (fact : Q old a d) : Q new b e := by
  subst new
  subst b
  subst e
  exact fact

open Lean Elab Term in
local elab "inferPaidCut% " term:term : term => elabTerm term none

open Lean Elab Term Meta in
local elab "paidCutResult% " kept:ident resolved:ident pages:ident : term => do
  let localValue (id : Syntax) : TermElabM Lean.Expr := do
    let some declaration := (← getLCtx).findFromUserName? id.getId | throwError "missing constructor input {id}"
    return declaration.toExpr
  let kept ← localValue kept
  let resolved ← localValue resolved
  let pages ← localValue pages
  let resolution ← inferType resolved
  let dataPages ← inferType pages
  let both := mkApp4 (Lean.mkConst ``And.intro) resolution dataPages resolved pages
  let keptType ← inferType kept
  let bothType := mkApp2 (Lean.mkConst ``And) resolution dataPages
  return mkApp4 (Lean.mkConst ``PProd.mk [← getLevel keptType, .zero]) keptType bothType kept both

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
noncomputable def cut_native_evidence (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
    (original : Memory w) (safe : (entry₀).Room (v₀) floor₀ w)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (old : Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (roles : Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (oldPitch : 0<(entry₀).previous.lanes) (rolePitch : 0<(entry₀).rolePitch)
    (lower : ∀x pg,(previousBank (entry₀).previous (entry₀).previousBase x pg).Fits w ((v₀).signedEnd floor₀))
    (oldRows : ∀x pg,Reads (previousBank (entry₀).previous (entry₀).previousBase x pg) (old pg x) (entry₀).previous.lanes (wired original))
    (roleLo : ∀x,((entry₀).role x).base+((entry₀).role x).size≤(v₀).signedEnd floor₀) (roleRoom : ∀x,(entry₀).previous.hosts*chunks G₀ (entry₀).rolePitch≤((entry₀).role x).size)
    (roleRows : ∀x,Reads ((entry₀).role x) (roles x) (entry₀).rolePitch (wired original))
    (active : Active) (hubs : Fin H₀→Cell 1) (actors : 0<(entry₀).clip.actorPitch)
    (act : Reads (entry₀).venue.actors active (entry₀).clip.actorPitch (wired original))
    (one : ∀h : Fin H₀,(wired original) ((entry₀).venue.hub.base+h.val)=((hubs h).val:Word w))
    (oldFit : Fintype.card prior.V≤(v₀).area.H)
    (oldR : Fin (v₀).area.H→Fin (A).degree→Option (Fin (v₀).area.H))
    (pick : ((A).stage.result nonneg).Choice)
    (board : (v₀).SelectedBoard oldFit oldR pick (donors original) (steps₀).parts)
    (chosen : HEq pick choice) (newFit : Fintype.card next.V≤(v₀).venue.hosts)
    (reciprocal : ∀a b j,oldR a j=some b→∃l,oldR b l=some a)
    (adjacency : ∀h j,(donors original) ((steps₀).adjacency.base+h.val*(A).degree+j.val)=(number (oldR h j):Word w))
    (cash : (v₀).SignedRoom floor₀ w) (older : 0<(v₀).markShape.oldLanes)
    (oldPrecision oldFloor : ℕ)
    (oldVenue : stageVenue prior oldFit ports.io (v₀).markShape.oldLanes oldPrecision oldFloor
      (prior.venueRoster oldFit) (donors original))
    (wires : ∀(x:Fin (2^k))(j:Fin (2*(A).cap)),(ports.io.wire x.val j.val).base+
      (v₀).area.H*chunks (S.groupCount i) (v₀).markShape.oldLanes≤oldFloor)
    (countRead : (donors original) ports.archive.count.base=(Fintype.card prior.V:Word w))
    (countLow : ports.archive.count.base<oldFloor) (place : oldFloor≤(v₀).donorEnd floor₀)
    (stock : ports.ArchiveFits ports.venue.k root) (carried : ports.ArchiveTags original)
    (depthAt : k=ports.venue.k)
    (bitsFit : (((entry₀).previous.size+2)*(entry₀).previous.nodes)*(entry₀).previous.lanes≤w)
    (growth : 0<S.capGain)
    (population : PhysicalOrdinary.SectionPopulation (v₀) (entry₀) S i)
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) := inferPaidCut% (
  let capacity:=DatePorts.registered_operand_header_room ports ticket op g tailBits p f drift degree payload seats root ordinary
    code.signed page₀ safe previous admission code.endFit
  let props:=issued_return_fields X G S br ticket before tail cut (books₀) tailBits payload seats ports.venue.lanes
    ports.io.roster ordinary
  have fixed:= (DatePorts.ordinary_registered_signed ports ticket op g tailBits p f drift degree payload seats
    root ordinary props.2.2.2).1
  have selectedMemory:=DatePorts.ordinary_signed_image ports ticket op g tailBits p f drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec original fixed
  let dateSpace:=registered_donor_extent X G S br ticket before tail cut op tailBits drift degree payload seats root ports ordinary
  have floorSame : (v₀).stageStart root = floor₀ := rfl
  have panelSame : (steps₀).parts = (entry₀).venue.panel := rfl
  have degreeSame : (fmt₀).degree = (A).degree := rfl
  have socketSame : (entry₀).clip.venue.socket.degree = (fmt₀).degree := rfl
  have rosterSame : (entry₀).venue.adjacency = ports.io.roster := rfl
  have pr : (steps₀).parts.base+(steps₀).parts.size≤(phys₀).donorEnd floor₀:=by
    have roof := congrArg₂ (fun (model : PhysicalOrdinary F _) (n : ℕ) => model.donorEnd n) fixed floorSame.symm
    calc
      _ = (entry₀).venue.panel.base+(entry₀).venue.panel.size := congrArg (fun b : Bank => b.base+b.size) panelSame
      _ ≤ _ := dateSpace.1
      _ = _ := roof.symm
  let cc : (phys₀).SignedRoom floor₀ w:=by simpa only [fixed] using cash
  have sourceDegree : (v₀).signed.degree = (A).degree := code.signed.degree.trans degreeSame
  have mm : (phys₀).MaterialRoom ((phys₀).materialStart floor₀) (steps₀).parts
      (PriorHeader.reverseRank (v₀).area.H (phys₀).signed.groups (phys₀).signed.lanes (A).degree ((phys₀).donorEnd floor₀)) w:=
    receiptRoomAt (fun (model : PhysicalOrdinary F _) start d => model.MaterialRoom (model.materialStart start)
      (steps₀).parts (PriorHeader.reverseRank (v₀).area.H model.signed.groups model.signed.lanes d (model.donorEnd start)) w)
      fixed floorSame sourceDegree exec.late.material
  have pre : PriorHeader.Room (steps₀).adjacency (v₀).area.H (phys₀).signed.groups (phys₀).signed.lanes
      (A).degree ((phys₀).donorEnd floor₀) w:=
    receiptRoomAt (fun (model : PhysicalOrdinary F _) start d => PriorHeader.Room (steps₀).adjacency
      (v₀).area.H model.signed.groups model.signed.lanes d (model.donorEnd start) w)
      fixed floorSame sourceDegree exec.late.ranks
  let sources : DescentOrdinaryVenueReturn.Sources := ⟨ports.archive.count,ports.io.roster,ports.io.hubs⟩
  have geo := receiptRoomAt (fun (model : PhysicalOrdinary F _) start _ => DescentOrdinaryVenueReturn.Room
    sources (model.materialEnd start) (v₀).area.H (v₀).area.D (v₀).venue.hosts (v₀).venue.degree w)
    fixed floorSame (d:=0) rfl exec.late.peers
  have marked := receiptRoomAt (fun (model : PhysicalOrdinary F _) start _ => model.MarkRoom start ports.io w)
    fixed floorSame (d:=0) rfl exec.late.mark
  have originalPeer := (v₀).at_signed_adjacency (R:=oldR) (m:=donors original)
    (parts:=(steps₀).parts) (floor:=floor₀) (input:=ports.io) (count:=ports.archive.count) (adj:=(steps₀).adjacency)
    cc pre mm geo marked adjacency
  have priorPeer : ∀h j,(wired original) (ports.io.roster.base+h.val*(fmt₀).degree+j.val)=(number (oldR h j):Word w):=by
    intro h j
    rw [←selectedMemory]
    exact originalPeer h j
  let peer : RealPeers:=oldR
  have near : ∀h j,(wired original) ((entry₀).venue.adjacency.base+(h.val*(entry₀).clip.venue.socket.degree+j.val))=
      (number (peer h j):Word w):=by
    intro h j
    have address := congrArg₂ (fun (bank : Bank) (d : ℕ) => bank.base+(h.val*d+j.val)) rosterSame socketSame
    have regroup := (Nat.add_assoc ports.io.roster.base (h.val*(fmt₀).degree) j.val).symm
    exact (congrArg (wired original) (address.trans regroup)).trans (priorPeer h j)
  let parts : Fin H₀→Fin G₀→DepotRAM.Parts (entry₀).clip.venue.socket:=board.material
  have panelPitch : 0<(entry₀).clip.panelPitch:=board.live
  have panel : Reads (entry₀).venue.panel (fun h g=>DepotRAM.combine (entry₀).clip.venue.socket (parts h g))
      (entry₀).clip.panelPitch (wired original):=by
    rw [←selectedMemory]
    exact (v₀).signed_original_panel (oldFit:=oldFit) (R:=oldR) (selected:=pick) (m:=donors original) (parts:=(steps₀).parts) («B»:=board) (floor:=floor₀) (input:=ports.io) (count:=ports.archive.count)
      (adj:=(steps₀).adjacency) cc pre mm pr geo
      marked
  let dims:=dims₀ age radix
  let sh:=ordinary_publication_shape X G S br ticket before tail cut ports op tailBits drift degree payload seats
    root ordinary previous (congrArg (fun n:ℕ=>n-2) archive.digits)
  let data:=(entry₀).venueWord (v₀) parts active hubs peer sh.2.1
  let books : Val₀ (v₀).reference.nameBits (v₀).reference.countBits:=fun col low=>
    groupValues dims.2.2.2 ((entry₀).registeredValues (v₀) sh.1 floor₀ (mat₀) old parts roles
      (Gather.reaching peer) data sh.2.2.1 sh.2.2.2 col low)
  let chip:=(entry₀).nativeChips (v₀) sh.1.toBirthShape parts
  let funded:=(v₀).vector_before floor₀
  have vecRoom : vecAt<2^w:=by
    obtain ⟨f₁,f₂,f₃,f₄,f₅,f₆,_,_,_⟩:=(v₀).ticket_source_order floor₀
    exact (funded.trans (f₁.trans (f₂.trans (f₃.trans (f₄.trans (f₅.trans f₆)))))).trans_lt capacity.ceiling
  let pub:=cut_signed_tagged_shelf X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec age previous page₀ original safe archive old parts roles oldPitch panelPitch
    rolePitch lower oldRows panel roleLo roleRoom roleRows active hubs peer actors act one near oldR pre.hosts priorPeer
    carried stock depthAt bitsFit (Nat.mul_pos admission.lanes admission.radix) vecRoom
  let ae := (entry₀).samePorts (phys₀)
  let mt : ae.Match (phys₀) floor₀ := selectedEntryMatch (entry₀) fixed (mat₀)
  let shape : (phys₀).VectorShape := (congrArg PhysicalOrdinary.VectorShape fixed).mpr (sh₀)
  let opRoom : (phys₀).OperandHeaderRoom floor₀ ae mt (ae.directory (phys₀) floor₀ mt).refs
      ((ae.directory (phys₀) floor₀ mt).refs page₀) w:=
    PhysicalOrdinary.selected_cut_header_room (same:=fixed) (entry:=entry₀) (m:=mat₀) (m':=mt)
      (p:=page₀) (q:=page₀) (pq:=HEq.rfl) capacity
  let accept : (phys₀).TicketAdmission floor₀ w (v₀).issuedSignedChart ae mt page₀:=
    PhysicalOrdinary.selected_cut_ticket_admission (same:=fixed) (entry:=entry₀) (m:=mat₀) (m':=mt)
      (p:=page₀) (q:=page₀) (pq:=HEq.rfl) code.signed (v₀).issuedSignedChart admission
  let measures:=registered_walk_dimensions X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
  let q : Fin (vx₀).lows:=⟨0,measures.2.2.2⟩
  have rightDegree : (v₀).venue.degree=(v₀).target.placement.degree := props.2.2.1
  have rightOld : stageVenue (v₀).prior oldFit ports.io (phys₀).markShape.oldLanes oldPrecision oldFloor
      ((v₀).prior.venueRoster oldFit) (donors original) := by
    rw [fixed]
    exact oldVenue
  have rightWires : ∀(x:Fin (2^(v₀).k))(j:Fin (2*(v₀).prior.placement.cap)),
      (ports.io.wire x.val j.val).base+(v₀).area.H*chunks ((v₀).schedule.groupCount (v₀).age)
        (phys₀).markShape.oldLanes≤oldFloor := by
    rw [fixed]
    exact wires
  have rightPath : breadth (phys₀).reference.degree=(phys₀).signed.reach := by
    exact measures.2.2.1.trans (congrArg breadth (v₀).issuedSignedChart.degree.symm)
  have bought : (phys₀).origin.preparationWords=(phys₀).originControlWords+(phys₀).originMouthWords+(phys₀).rootSourceSize := by
    rw [fixed]
    exact (base₀).registered_reservation ports floor₀
  have fullEnd : (phys₀).endAddress floor₀<2^w := by
    rw [fixed]
    exact code.endFit
  have wordFit : (phys₀).resolver.lanes*DescentPackedOperand.unit (phys₀).resolver.size≤w/2 := by
    rw [fixed]
    exact code.packed
  have limit : 22*(fmt₀).cap+10<2^((phys₀).resolver.size+2) :=
    DatePorts.registered_ticket_ordinal_room ports ticket op g tailBits p f drift degree payload seats root ordinary growth age
  have cutDate := donor_date_eq X G S br ticket before tail cut
  have matcherArea : (v₀).area=(DonorDate.atDate G S g k i p).schedule (v₀).payload (v₀).seats (v₀).bitsPerField := by
    rw [← cutDate]
    change ticket.ordinaryArea (Nat.clog 2 (S.hostSize i)) (S.censusBits p) payload
      (base₀).unit (DescentTerminalEpochBits.width G.C) seats = _
    rw [props.2.1]
    rfl
  have rightMatcher : (v₀).area.Space ports.io w floor₀ := by
    rw [matcherArea,←floorSame]
    exact exec.matcher
  let normalized:=(v₀).original_resolver_keys_tagged (oldFit:=oldFit) (R:=oldR) (selected:=pick) (m:=donors original)
    (parts:=(steps₀).parts) («B»:=board) (choiceEq:=chosen) (wide:=newFit) (age:=age) (radix:=radix)
    (reciprocal:=reciprocal) (floor:=floor₀) (input:=ports.io) (count:=ports.archive.count) (adj:=(steps₀).adjacency)
    cc pre mm pr adjacency geo
    marked (by simpa only [fixed] using older)
    rightDegree rightMatcher oldPrecision oldFloor rightOld
    rightWires countRead countLow (by simpa only [fixed] using place)
    ae mt shape (by simpa only [fixed] using code.blocks) (by simpa only [fixed] using population.compact)
    (by simpa only [fixed] using population.resolver.2.trans population.vector.2) page₀ opRoom rfl chip books
    q (by simpa only [fixed] using measures.1) rightPath
    (pub.2.2.1 q) (by simpa only [fixed] using dims.2.1) (by simpa only [fixed] using dims.2.2.2) rfl accept
    (PhysicalOrdinary.selected_cut_chip_read (oldChip:=chip) (newChip:=chip) fixed (entry₀) selectedMemory HEq.rfl pub.2.2.2.2) (PhysicalOrdinary.selected_cut_chip_span fixed (entry₀) pub.2.2.2.1)
    (by simpa only [fixed] using dims.2.2.1) (by simpa only [fixed] using dims.1)
    (PhysicalOrdinary.selected_cut_mounted_pages (same:=fixed) (entry:=entry₀) (matched:=mat₀) (newMatch:=mt) (oldBooks:=books) (newBooks:=books) (bookEq:=HEq.rfl) (memory:=selectedMemory.symm) pub.1)
    bought
    fullEnd wordFit
    (PhysicalOrdinary.selected_cut_operand_book_tags (same:=fixed) (shape:=sh₀) (newShape:=shape) (oldBooks:=books) (newBooks:=books) (bookEq:=HEq.rfl) pub.2.1)
    limit
  let vectors:=DatePorts.registered_vector_pages_at_metadata ports ticket op g tailBits p f drift degree
    payload seats root ordinary w shelfHeader headerBase pos code exec original admission dims.1 books pub.1
  have printed:=DatePorts.normalized_keys_on_date ports ticket op g tailBits p f drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec original fixed mt shape (by simpa only [fixed] using code.blocks)
    fullEnd wordFit
    (a:=DescentPackedOperand.outputWidth (rc₀).size) _ normalized
  let auditedPopulationRows {K I : Type} [Field K] (v : PhysicalOrdinary K I) (E : PhysicalOrdinary.ArgumentEntry v) (sched : AtomSchedule) (ix : ℕ)
        (pop : PhysicalOrdinary.SectionPopulation v E sched ix) (fixed : v = v.withIssuedSigned)
      (radix : sched.radix=2^v.k) :
      v.paletteShape.hosts=v.bornBook.hosts ∧
      v.withIssuedSigned.resolver.hosts≤v.withIssuedSigned.material.hosts ∧
      v.withIssuedSigned.resolver.groups=v.withIssuedSigned.material.groups ∧
      sched.groupCount ix=v.withIssuedSigned.material.groups*v.withIssuedSigned.material.blocks := by
    have blocks : v.withIssuedSigned.material.blocks=2^v.k := rfl
    have hs : v.resolver.hosts≤v.material.hosts := pop.compact
    have gs : v.resolver.groups=v.material.groups := pop.resolver.2.trans pop.vector.2
    have groupSize : v.material.groups=sched.groupCount (ix+1) := pop.material.2
    refine ⟨pop.vector.1.trans pop.born.1.symm,?_,?_,?_⟩
    · exact (congrArg (fun y : PhysicalOrdinary K I => y.resolver.hosts ≤ y.material.hosts) fixed).mp hs
    · exact (congrArg (fun y : PhysicalOrdinary K I => y.resolver.groups=y.material.groups) fixed).mp gs
    · have moved := (congrArg (fun y : PhysicalOrdinary K I => y.material.groups) fixed).symm.trans groupSize
      rw [moved,blocks,←radix]
      exact pop.group_partition.symm
  let populated := auditedPopulationRows (v₀) (entry₀) S i population fixed.symm radix
  let retained : CutStores X G S (f:=f) (g:=g) (p:=p) (radix:=radix) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original :=
    {old:=old, roles:=roles, active:=active, hubs:=hubs, oldFit:=oldFit, rotor:=oldR, pick:=pick,
     board:=board, selected:=chosen, parts:=parts, material:=rfl, actors:=act, flags:=one,
     oldRead:=oldRows, roleRead:=roleRows, panel:=panel, peers:=near, inputs:=sh.1, width:=sh.2.1,
     names:=sh.2.2.1, ranks:=sh.2.2.2, groups:=dims.2.2.2, books:=books, registered:=fun _ _=>rfl,
     entryFits:=safe, oldPitch:=oldPitch, rolePitch:=rolePitch, oldBanks:=lower,
     roleLo:=roleLo, roleRoom:=roleRoom, actorsPositive:=actors, admission:=admission, previousGroups:=previous,
     primitiveHosts:=populated.1,
     hostBound:=populated.2.1,
     groupBound:=populated.2.2.1,
     groupSplit:=populated.2.2.2,
     nextFit:=newFit,
     resolvedWords:=by
       intro rotor₂ same
       subst rotor₂
       intro age₂ wide₂ bands₂ reciprocal₂ hostBound₂ groupBound₂ matching₂ shape₂
       dsimp only
       intro room₂ index₂
       exact printed index₂}
  paidCutResult% retained normalized vectors)

open scoped OAI.Hierarchy

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun others =>
    "cut_native_shelves" :: "cut_resolver_keys" :: others

theorem cut_native_shelves :
    type_of% (proofField% cut_native_evidence [PProd.snd]) :=
  no_implicit_lambda% proofField% cut_native_evidence [PProd.snd]

/-- The physical operand-key projection of the common native shelves. -/
theorem cut_resolver_keys :
    type_of% (proofField% cut_native_evidence [PProd.snd, And.left]) :=
  no_implicit_lambda% proofField% cut_native_evidence [PProd.snd, And.left]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
