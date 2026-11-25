import OAI.Hierarchy.ProofField
import OAI.Hierarchy.DescentNamedCutArgumentWords
import OAI.Hierarchy.DescentOrdinarySignedActorHeaders
import OAI.Hierarchy.DescentRegisteredIncomingVenue

namespace OAI
/-! Registered operand returns from the accepted board and the retained predecessor on entry. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option cleanup.letToHave false


variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {hu : 0 ≤ (((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ))*((S.epochPower^S.priceExponent):ℝ))} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=(GroupStage.depthBound (atRound S.rounds) n f g)) (t:=S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


set_option quotPrecheck false
variable {bn bd : ℕ} (net : NonlinearExpanders.Graph bn bd) (perDate headerAt : ℕ→ℕ)
variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "seats" => perDate i
local notation "shelfHeader" => headerAt i
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

variable (w headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload (perDate i) root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload (perDate i) root ordinary
      w (headerAt i) headerBase code)
open Lean Elab Term in
local elab "cutBoardApply% " head:term:arg "[" xs:term,* "]" : term => do
  let fn ← elabTerm head none
  return mkAppN fn (← xs.getElems.mapM fun x => elabTerm x none)

local notation "dateApplied" function:arg => cutBoardApply% function [
    F, P, (inferInstance : Field F), G, S, (0:ℕ), k, i, z, D, z', D', wire, s,
    price, fee, rate, bits, W, prior, nonneg, T, choice, norm, next,
    ports, ticket, op, g, tailBits, p, f, drift, degree, payload, (perDate i),
    root, ordinary, w, (headerAt i), headerBase, pos, code, exec]
local notation:max "wired" m:arg => (dateApplied (@DatePorts.ordinarySignedMemory)) m

local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation:max "donors" m:arg => (dateApplied (@DatePorts.ordinaryDonorMemory)) m
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local


local notation "menu₀" => (⟨net,op,g,tailBits,p,f,drift,degree,payload,perDate,ordinary,headerAt,headerBase⟩:
  RegisterTimeline.Menu bn bd)
local notation "realHosts" h:arg => prior.vertex.trans (Fin.castLEEmb h)
local notation "realRotor" h:arg => hostRotor (realHosts h) (hostRoster prior.placement ((realHosts h).trans Fin.valEmbedding))
local notation "date₀" => DonorDate.atDate G S g k i p
/- Infer the concrete pair type with the local selected board and its proofs in scope. -/
open Lean Meta Elab Term in
local elab "cutBoardResult% " x:term : term => do
  let value ← elabTerm x none
  inferType value
open Lean Parser.Term in
local macro doc:(docComment)? "cutBoardDefinition " n:ident bs:bracketedBinder* " := " b:term : command =>
  `($[$doc:docComment]? noncomputable def $n $bs* : cutBoardResult% ($b) := $b)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 450000 in
cutBoardDefinition cut_argument_model_on_board (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
    (original : Memory w) (safe : (entry₀).Room (v₀) floor₀ w)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (old : Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (roles : Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (oldPitch : 0<(entry₀).previous.lanes) (rolePitch : 0<(entry₀).rolePitch)
    (lower : ∀ (x : Fin (entry₀).previous.blocks) (page : Pages (entry₀).previous.operands),
      (previousBank (entry₀).previous (entry₀).previousBase x page).Fits w ((v₀).signedEnd floor₀))
    (oldRows : ∀ (x : Fin (entry₀).previous.blocks) (page : Pages (entry₀).previous.operands),
      Reads (previousBank (entry₀).previous (entry₀).previousBase x page) (old page x) (entry₀).previous.lanes (wired original))
    (roleLo : ∀x,((entry₀).role x).base+((entry₀).role x).size≤(v₀).signedEnd floor₀) (roleRoom : ∀x,(entry₀).previous.hosts*chunks G₀ (entry₀).rolePitch≤((entry₀).role x).size)
    (roleRows : ∀x,Reads ((entry₀).role x) (roles x) (entry₀).rolePitch (wired original))
    (offered : let boardState : Memory w := donors original
      let partBank : Bank := (steps₀).parts
      ∃(wide:Fintype.card prior.V≤(v₀).area.H)(pick:((A).stage.result nonneg).Choice),
      HEq choice pick ∧ Nonempty ((v₀).SelectedBoard (w:=w) wide (realRotor wide) pick boardState partBank))
    (cells : RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher : (ordinary i).payload=payload ∧ (ordinary i).unit=(date₀).amount)
    (priorHeld : ports.held prior root original) (newFit:Fintype.card next.V≤(v₀).venue.hosts)
    (cash : (v₀).SignedRoom floor₀ w) (actorPitch : 0<(v₀).area.lanesAt)
    (stock : ports.ArchiveFits ports.venue.k root) (carried : ports.ArchiveTags original)
    (depthAt : k=ports.venue.k)
    (bitsFit : (((entry₀).previous.size+2)*(entry₀).previous.nodes)*(entry₀).previous.lanes≤w)
    (growth : 0<S.capGain)
    (population : PhysicalOrdinary.SectionPopulation (v₀) (entry₀) S i)
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) :=
  let wide:=offered.choose
  let pick:=offered.choose_spec.choose
  let observed:=Classical.choice offered.choose_spec.choose_spec.2
  let truth : HEq pick choice:=offered.choose_spec.choose_spec.1.symm
  let entered:=registered_incoming_venue X G S br ticket before tail cut op tailBits drift degree payload root ports
    ordinary net perDate headerAt headerBase w original age cells matcher priorHeld
  let originalPose:stageVenue prior wide ports.io (v₀).area.lanesAt (v₀).bitsPerField root (prior.venueRoster wide) original:=
    entered.choose_spec.1
  let pose:=(dateApplied (@DatePorts.ordinary_signed_pose)) (countBits := (v₀).bitsPerField) original wide originalPose
  let floorPaid : root≤(v₀).donorEnd floor₀:=by
    have first:root≤floor₀:=by
      change root≤(v₀).profileRepack.endAddress root
      rw [(v₀).profileRepack.translate];exact Nat.le_add_right ..
    rw [(v₀).donor_shift]
    exact first.trans (Nat.le_add_right ..)
  let persisted:=(dateApplied (@DatePorts.ordinary_retained_memories)) original
  let archived:=(dateApplied (@DatePorts.ordinary_signed_archive_frame)) original
  let keep (j:ℕ)(hj:j<root):(donors original) j=original j:=
    (persisted.1 j (hj.trans_le floorPaid)).symm.trans (archived j hj)
  let oldHere:=stageVenue_below prior wide ports.io (v₀).area.lanesAt (v₀).bitsPerField root (prior.venueRoster wide)
    original (donors original) originalPose entered.choose_spec.2.1 keep
  let counted:ports.archive.count.base<root:=
    (Nat.lt_add_of_pos_right (Nat.two_pow_pos ports.archive.count.bits)).trans_le cells.room.header.count.2.2
  let adjacency (h:Fin (v₀).area.H)(j:Fin (A).degree) :
      (donors original) ((steps₀).adjacency.base+h.val*(A).degree+j.val)=(number ((realRotor wide) h j):Word w):=by
    let column:=Fin.cast prior.branch j
    have read:=oldHere.2.1.roster h column
    have rank:(realHosts wide).trans Fin.valEmbedding=prior.vertex.trans Fin.valEmbedding:=by
      ext vertex
      rfl
    have adjBase : (steps₀).adjacency.base = (ports.io.ports D).roster.base := rfl
    rw [adjBase]
    simp only [prior.branch, Reached.venueRoster, DescentHaloWalkRAM.number, column,
      Fin.val_cast, Fin.cast_cast, Fin.cast_refl, rank, DescentPackedColony.target, Nat.add_assoc, id_eq] at read ⊢
    exact read
  let table:=cut_argument_evidence X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary w
    shelfHeader headerBase pos code exec age previous original safe archive old roles oldPitch rolePitch lower oldRows
    roleLo roleRoom roleRows (Prepare.actors A (Function.Embedding.refl _) (realHosts wide))
    (Census.hub A (realHosts wide)) actorPitch pose.1 pose.2 wide (realRotor wide) pick observed truth newFit
    (extended_reciprocal A (realHosts wide) ((realHosts wide).trans Fin.valEmbedding)) adjacency cash
    actorPitch (v₀).bitsPerField root oldHere entered.choose_spec.2.1
    ((keep _ counted).trans entered.choose_spec.2.2) counted floorPaid stock carried depthAt bitsFit growth population admission
  let faithful : table.1.Canonical := ⟨rfl,rfl,rfl⟩
  let result := PProd.mk (β := table.1.Canonical) table faithful
  result

cutBoardDefinition cut_argument_evidence_on_board (age : i<S.length) (previous : ports.venue.groups=S.groupCount i)
    (original : Memory w) (safe : (entry₀).Room (v₀) floor₀ w)
    (archive : DatePorts.ArchiveWidths G S op ports k tailBits p drift degree payload i)
    (old : Pages (entry₀).previous.operands→Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin (entry₀).previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits (entry₀).previous))
    (roles : Fin (entry₀).previous.blocks→Fin (entry₀).previous.hosts→Fin G₀→Cell ((pop₀).roleBits*(pop₀).nodes))
    (oldPitch : 0<(entry₀).previous.lanes) (rolePitch : 0<(entry₀).rolePitch)
    (lower : ∀ (x : Fin (entry₀).previous.blocks) (page : Pages (entry₀).previous.operands),
      (previousBank (entry₀).previous (entry₀).previousBase x page).Fits w ((v₀).signedEnd floor₀))
    (oldRows : ∀ (x : Fin (entry₀).previous.blocks) (page : Pages (entry₀).previous.operands),
      Reads (previousBank (entry₀).previous (entry₀).previousBase x page) (old page x) (entry₀).previous.lanes (wired original))
    (roleLo : ∀x,((entry₀).role x).base+((entry₀).role x).size≤(v₀).signedEnd floor₀) (roleRoom : ∀x,(entry₀).previous.hosts*chunks G₀ (entry₀).rolePitch≤((entry₀).role x).size)
    (roleRows : ∀x,Reads ((entry₀).role x) (roles x) (entry₀).rolePitch (wired original))
    (offered : let boardState : Memory w := donors original
      let partBank : Bank := (steps₀).parts
      ∃(wide:Fintype.card prior.V≤(v₀).area.H)(pick:((A).stage.result nonneg).Choice),
      HEq choice pick ∧ Nonempty ((v₀).SelectedBoard (w:=w) wide (realRotor wide) pick boardState partBank))
    (cells : RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher : (ordinary i).payload=payload ∧ (ordinary i).unit=(date₀).amount)
    (priorHeld : ports.held prior root original) (newFit:Fintype.card next.V≤(v₀).venue.hosts)
    (cash : (v₀).SignedRoom floor₀ w) (actorPitch : 0<(v₀).area.lanesAt)
    (stock : ports.ArchiveFits ports.venue.k root) (carried : ports.ArchiveTags original)
    (depthAt : k=ports.venue.k)
    (bitsFit : (((entry₀).previous.size+2)*(entry₀).previous.nodes)*(entry₀).previous.lanes≤w)
    (growth : 0<S.capGain)
    (population : PhysicalOrdinary.SectionPopulation (v₀) (entry₀) S i)
    (admission : (v₀).TicketAdmission floor₀ w code.signed (entry₀) (mat₀) page₀) :=
  (cut_argument_model_on_board X G S br ticket before tail cut net perDate headerAt ports op tailBits drift
    degree payload root ordinary w headerBase pos code exec age previous original safe archive old roles
    oldPitch rolePitch lower oldRows roleLo roleRoom roleRows offered cells matcher priorHeld newFit cash
    actorPitch stock carried depthAt bitsFit growth population admission).1

open scoped OAI.Hierarchy

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun others =>
    "cut_argument_shelves_on_board" :: "cut_argument_words_on_board" :: others

theorem cut_argument_shelves_on_board :
    type_of% (proofField% cut_argument_evidence_on_board [PProd.snd]) :=
  no_implicit_lambda% proofField% cut_argument_evidence_on_board [PProd.snd]

/-- The normalized job projection of the two attained shelves. -/
theorem cut_argument_words_on_board :
    type_of% (proofField% cut_argument_evidence_on_board [PProd.snd, And.left]) :=
  no_implicit_lambda% proofField% cut_argument_evidence_on_board [PProd.snd, And.left]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
