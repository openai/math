import OAI.Hierarchy.DescentNamedCutResolverKeys
import OAI.Hierarchy.DescentNamedCutResolverMemory

namespace OAI
/-! The normalized packed words at their observed chronological ordinary cut. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch DescentPacking DescentCompiler DescentKernelHistory.BitDescription
open DescentPackedProfileWide DescentPackedProfileWindow DescentPackedProfileArchive DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentPackedColony DescentStageEdgeReceipt DescentGroupPeerOrder DescentHostDirectory
open DescentHaloWalkRAM
open scoped Classical Fin.CommRing
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
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
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded

local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) room.slots⟩:Fin (7*(v).vector.operands))

variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "phys" => (v).withIssuedSigned
local notation "donors" m => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m
open DescentDatedPriorOperand DescentPackedColony
local notation "E₀" => (A).samePorts (phys)
local notation "signed₀" m => ((v).signedReturn floor prior.io prior.archive.count (steps).parts (steps).adjacency w).image (donors m)
local notation "actual₀" m => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec m

set_option maxRecDepth 4096 in
/-- The output of the selected physical signed model, on its actual mounted tape, at
the consecutive metadata and argument writers of the original ticket. The cell family
is preserved literally, including every decoded operand and its padding lanes. -/
private def packActualCutArgumentWords (m : Memory w) (fixed : phys=v)
    (mt : (E₀).Match phys floor) (shape : (phys).VectorShape)
    (blocks : (phys).resolver.blocks=(phys).material.blocks)
    (limit : (phys).endAddress floor<2^w)
    (wide : (phys).resolver.lanes*DescentPackedOperand.unit (phys).resolver.size≤w/2)
    {a : ℕ} (values : Fin (v).resolver.jobs→Fin (v).resolver.hosts→Fin (v).resolver.groups→Cell a)
    {Record : Type*} {vectors : Prop} (native : PProd Record ((∀j,Reads (Banks.wordBank (phys).resolver ((phys).normalizedEnd floor) j) (values j)
      (phys).resolver.lanes
      (((phys).routedArguments floor ((E₀).directory (phys) floor mt).refs
        ((phys).nativeTicketExpr floor (v).issuedSignedChart (E₀) mt shape blocks)
        ((phys).nativeTicketPreparation floor w (v).issuedSignedChart (E₀) mt shape blocks pg)
        shape limit wide).image ((E₀).mountedTape (phys) floor (signed₀ m)))) ∧ vectors)) :
    PProd Record ((∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j) (values j)
      (v).resolver.lanes (actual₀ m)) ∧ vectors) :=
  PProd.mk native.1 ⟨normalized_keys_on_date prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec m fixed mt shape blocks limit wide values native.2.1, native.2.2⟩


end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000

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
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)

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
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open Lean Meta Elab Term in
local elab "actualCutPackingType% " x:term : term => do
  let value ← elabTerm x none
  inferType value

private theorem matchOnIssuedModel {K I : Type} [Field K] {old new : PhysicalOrdinary K I}
    (entry : old.ArgumentEntry) (same : new = old) {start : ℕ} (proof : entry.Match old start) :
    (entry.samePorts new).Match new start := by
  subst new
  cases entry
  exact proof

include before tail cut in
/-- The authenticated selected board supplies the original packed keys to the consecutive argument writer. -/
noncomputable def cut_argument_evidence (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
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
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) : actualCutPackingType% (
  let native:=cut_native_evidence X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission
  let props:=issued_return_fields X G S br ticket before tail cut (books₀) tailBits payload seats ports.venue.lanes
    ports.io.roster ordinary
  have fixed:=(DatePorts.ordinary_registered_signed ports ticket op g tailBits p f drift degree payload seats
    root ordinary props.2.2.2).1
  let E := (entry₀).samePorts (phys₀)
  let mt : E.Match (phys₀) floor₀ := matchOnIssuedModel (entry₀) fixed (mat₀)
  let shape : (phys₀).VectorShape := fixed.symm ▸ (sh₀)
  have blocks : (phys₀).resolver.blocks=(phys₀).material.blocks := fixed.symm ▸ code.blocks
  have fullEnd : (phys₀).endAddress floor₀<2^w := fixed.symm ▸ code.endFit
  have wordFit : (phys₀).resolver.lanes*DescentPackedOperand.unit (phys₀).resolver.size≤w/2 :=
    fixed.symm ▸ code.packed
  DatePorts.packActualCutArgumentWords ports ticket op g tailBits p f drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec original fixed mt shape blocks fullEnd wordFit (a:=DescentPackedOperand.outputWidth (rc₀).size) _ native
  ) :=
  let native:=cut_native_evidence X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission
  let props:=issued_return_fields X G S br ticket before tail cut (books₀) tailBits payload seats ports.venue.lanes
    ports.io.roster ordinary
  have fixed:=(DatePorts.ordinary_registered_signed ports ticket op g tailBits p f drift degree payload seats
    root ordinary props.2.2.2).1
  let E := (entry₀).samePorts (phys₀)
  let mt : E.Match (phys₀) floor₀ := matchOnIssuedModel (entry₀) fixed (mat₀)
  let shape : (phys₀).VectorShape := fixed.symm ▸ (sh₀)
  have blocks : (phys₀).resolver.blocks=(phys₀).material.blocks := fixed.symm ▸ code.blocks
  have fullEnd : (phys₀).endAddress floor₀<2^w := fixed.symm ▸ code.endFit
  have wordFit : (phys₀).resolver.lanes*DescentPackedOperand.unit (phys₀).resolver.size≤w/2 :=
    fixed.symm ▸ code.packed
  DatePorts.packActualCutArgumentWords ports ticket op g tailBits p f drift degree payload seats root ordinary
    w shelfHeader headerBase pos code exec original fixed mt shape blocks fullEnd wordFit (a:=DescentPackedOperand.outputWidth (rc₀).size) _ native

theorem cut_argument_shelves (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
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
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) : actualCutPackingType% (
  (cut_argument_evidence X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission).2
  ) :=
  (cut_argument_evidence X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission).2

/-- The normalized key words in the same reached memory. -/
theorem cut_argument_words (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
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
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) : actualCutPackingType% (
  (cut_argument_shelves X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission).1
  ) :=
  (cut_argument_shelves X G S br ticket before tail cut ports op tailBits drift degree payload seats root
    ordinary w shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch
    lower oldRows roleLo roleRoom roleRows active hubs actors act one oldFit oldR pick board chosen newFit reciprocal
    adjacency cash older oldPrecision oldFloor oldVenue wires countRead countLow place stock carried depthAt bitsFit
    growth population admission).1

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
