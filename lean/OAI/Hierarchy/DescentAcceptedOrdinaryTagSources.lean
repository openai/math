import OAI.Hierarchy.DescentRegisteredAcceptedArguments
import OAI.Hierarchy.DescentReturnedArgumentTags
import OAI.Hierarchy.DescentNamedOrdinaryArchiveTags
import OAI.Hierarchy.DescentReturnedAcceptedVenueRooms
import OAI.Hierarchy.DescentNamedAllRegisterMoves
import OAI.Hierarchy.DescentOrdinaryTagBounds

namespace OAI
/-! Reached archive tag sources on the original selected ordinary trajectory. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option hygiene false
local notation "s" => S.firstWidth G.b p
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
    (frozen drift degree payload lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial

open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
local notation "pitch" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "issue" => RegisterTimeline.issued (w:=w) traces menu
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial


open DescentCompiler.TerminalScale DescentGroupPeerOrder DescentStageEdgeReceipt
open DescentColonies DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentGroupPeerOrder DescentHaloWalkRAM
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu


local notation "walk₀" z => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z

variable (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=Fin.ofNat (2^w) (packed a.src.pin votes pitch j.val).val)
    {W : MarkedWorld F 0 pins widths} {i z D z' D' : ℕ} {rate : ℝ} {nonneg : 0 ≤ fee}
    {prior : Reached W G price fee S k i z D (S.epochPower^S.priceExponent) s} {T : StageInput W G rate fee}
    {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' (S.epochPower^S.priceExponent) s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path (trace (walk₀ votes)).origin.source prior) (after : Path next (trace (walk₀ votes)).target)
    (located : (before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (accepted : before.selections.length+1<((ch).rows votes).length ∨ (ch).read votes=some (walk₀ votes))
    (codeRoom : DatePorts.OrdinaryCodeRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom (cursor i).ports ticket op g frozen p f drift degree payload
      ((menu).seats i) (cursor i).floor (menu).ordinary w ((menu).profile i) header codeRoom)
    (cells : RegisterTimeline.Geometry G S menu k w i (cursor i))
    (old : (cursor i).ports.held prior (cursor i).floor (liveCPU m i))
    (height : 0<S.height) (age : i<S.length) (floorFit : (cursor i).floor<2^w)
    (keys : S.groupCount i*hostRows (S.hostSize i)*S.radix<2^w)
    (counts : (S.groupCount i*hostRows (S.hostSize i)*S.radix)*2^(8+S.capGain*i)<2^w)
    (grainRoom : 2*DescentPackedEpochShelves.unit G.C≤payload/2)
    (layoutRoom : (menu).seats i*(G.C+8+8*G.k)<2^w)

set_option hygiene true
local notation "point₀" => cursor i
local notation "ports₀" => (point₀).ports
local notation "fund₀" => (v₂ i ticket)
local notation "seed₀" => (OrdinaryBooks.atDate G S op g k i p frozen drift degree payload ((menu).seats i) ports₀).onTicket
  ticket g frozen p f payload ((menu).seats i) (ports₀).venue.lanes (ports₀).io.roster (menu).ordinary
local notation "floor₀" => (seed₀).stageStart (point₀).floor
local notation "entry₀" => (seed₀).registeredEntry ports₀ floor₀
local notation "mat₀" => (seed₀).registered_match ports₀ floor₀ (Nat.le_max_left (ports₀).argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population fund₀ floor₀
local notation "wired₀" => DatePorts.ordinarySignedMemory ports₀ ticket op g frozen p f drift degree payload
  ((menu).seats i) (point₀).floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i)
local notation "pg₀" => (⟨0,Nat.mul_pos (by decide : 0<7) codeRoom.slots⟩:Fin (7*(fund₀).vector.operands))
open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open DescentBundleHistory DescentLocalArchiveOrder DescentKernelHistory DescentPrimitivePalette
open scoped Classical Fin.CommRing

set_option maxHeartbeats 1600000 in
include protected_ beforeHeader lower original located accepted exec cells old height age floorFit keys counts grainRoom layoutRoom in
theorem accepted_header_venue
    (venue : Branch.PositiveVenueRooms (X:=X) (G:=G) (S:=S) ticket op frozen drift degree payload (point₀).floor
      ports₀ (menu).ordinary (menu).seats w codeRoom) :
    Fintype.card next.V≤(fund₀).venue.hosts ∧ (fund₀).resolver.hosts≤(fund₀).venue.hosts ∧
    DatePorts.returnedVenue ports₀ ticket op g frozen p f drift degree payload ((menu).seats i)
      (point₀).floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i) :=by
  have groups : 0<S.baseGroups:=by
    rw [cells.room.scheduled.choose_spec.choose_spec.choose_spec.choose_spec]
    exact Nat.two_pow_pos _
  have paid:=accepted_venue_with_rooms X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial protected_ beforeHeader lower votes m original ticket before after located
    accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom groups venue
  have starts:=cells.room.initialSites.choose_spec
  have rad:=cells.room.radix
  have newFit : Fintype.card next.V≤(fund₀).venue.hosts:=by
    change Fintype.card next.V≤NativePitch.incomingHosts S (i+1)
    rw [NativePitch.incomingHosts_eq starts rad _ age]
    exact next.valid.host
  have live : 0 < S.hostSize i := by
    have initialSites : 0 < S.initialSites := starts.symm ▸ Nat.two_pow_pos _
    have radix : 0 < S.radix := rad.symm ▸ Nat.two_pow_pos _
    exact Nat.mul_pos initialSites (pow_pos (Nat.mul_pos (Nat.two_pow_pos _) radix) _)
  have dated := cells.room.scheduled.choose_spec.choose_spec.choose_spec.choose_spec
  have pop:PhysicalOrdinary.SectionPopulation (fund₀) (entry₀) S i:=by
    exact DatePorts.registered_section_population ports₀ ticket op g frozen p f drift degree payload ((menu).seats i)
      (ports₀).venue.lanes (ports₀).io.roster (menu).ordinary floor₀ dated live rad
  have crop:=pop.compact.trans_eq pop.venue.1.symm
  exact ⟨newFit,crop,paid⟩

attribute [local irreducible] SeedNamed.issued Origin.source
set_option cleanup.letToHave false
set_option maxHeartbeats 4000000 in
include protected_ beforeHeader lower original located accepted exec cells old height age floorFit keys counts grainRoom layoutRoom in
theorem accepted_tag_sources {K : ℕ} (B : BitDescription W) (number : Local B)
    (places : DatePorts.RangeRoom ports₀ prior B) (shape : WorldShape p K B)
    (labels : NodeOrder.All B→Label G s (S.grainAt G.b p 0) op)
    (pointer : NodeOrder.All B→ℕ→Pointer) (flags : Fin (2^(ports₀).venue.k)→Fin (ports₀).nodes→Fin (ports₀).operandHosts→Fin (ports₀).venue.groups→ℕ)
    (stored : DatePorts.ArchiveRead ports₀ prior B number places shape op labels pointer flags (liveCPU m i))
    (slots : (ports₀).RoleRows) (rolePositive : 0<(ports₀).roleLanes) (carried : (ports₀).ArchiveTags (liveCPU m i))
    (venue : Branch.PositiveVenueRooms (X:=X) (G:=G) (S:=S) ticket op frozen drift degree payload (point₀).floor
      ports₀ (menu).ordinary (menu).seats w codeRoom) (word : payload≤w) :
    RegisterTimeline.OrdinaryTagSources (traces) (menu) initial m ticket :=by
  let data:=accepted_argument_shelves X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial protected_ beforeHeader lower votes m original ticket before after located
    accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom
    B number places shape labels pointer flags stored slots rolePositive carried venue word
  let receipts := accepted_header_venue X G S ordinary reset branch positive room shorten w fit
    board op frozen drift degree payload lo header initial protected_ beforeHeader lower votes m original
    ticket before after located accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom venue
  have newFit := receipts.1
  have crop := receipts.2.1
  have paid := receipts.2.2
  have observed:=DatePorts.returned_writer_rows ports₀ ticket op g frozen p f drift degree payload ((menu).seats i)
    (point₀).floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec
    (liveCPU m i) newFit crop paid _ _ data.2 data.1
  refine ⟨prior.placement.fieldBits,codeRoom,exec,?_,?_,?_,observed⟩
  · let step : (trace (walk₀ votes)).path.Event i := .ordinary before ticket after located
    let event : RunTrace.Events (traces) i := ⟨walk₀ votes, step⟩
    intro r y issuedAt
    apply all_registered_moves X G S ordinary reset branch positive room shorten w (menu)
      rfl rfl rfl i (point₀) r event y _ issuedAt
    exact ⟨prior.placement.fieldBits,codeRoom,rfl⟩
  · have meter:=Branch.ordinary_meter_roof X G S (trace (walk₀ votes)) ticket before after located op frozen
      drift degree payload ((menu).seats i) (point₀).floor ports₀ (menu).ordinary header
    exact meter.2.2.trans ((fund₀).donor_before_arguments floor₀)
  · have meter:=Branch.ordinary_meter_roof X G S (trace (walk₀ votes)) ticket before after located op frozen
      drift degree payload ((menu).seats i) (point₀).floor ports₀ (menu).ordinary header
    have floorLo:=lower.trans_le (RegisterTimeline.initial_below_cursor (issue) initial i)
    have originalLow : (point₀).floor≤floor₀:=by
      change _≤(seed₀).profileRepack.endAddress (point₀).floor
      rw [(seed₀).profileRepack.translate];exact Nat.le_add_right ..
    let period:=(DonorDate.atDate G S g k i p).schedule payload ((menu).seats i) (fund₀).bitsPerField
    have start : floor₀≤period.rotationEnd (ports₀).io.roster floor₀:=by
      have rotate:=period.rotation_add (ports₀).io.roster 0 floor₀
      simp only [Nat.add_zero] at rotate
      rw [rotate]
      omega
    exact (floorLo.trans_le (originalLow.trans (start.trans meter.1))).trans meter.2.1

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
