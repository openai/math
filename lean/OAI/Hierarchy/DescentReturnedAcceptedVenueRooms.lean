import OAI.Hierarchy.DescentAcceptedRegisteredVenue
import OAI.Hierarchy.DescentNamedPositiveVenueRooms

namespace OAI
/-! # Accepted ballots return the full successor venue on the original machine with its attained dated ceilings -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w)
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
local notation "pos₀" => cursor
local notation "v₂" i:arg tick:arg => DatePorts.ordinaryModel (cursor i).ports tick op g frozen p f drift degree
  payload ((menu).seats i) (cursor i).floor (menu).ordinary
local notation "liveCPU" => DateCode.history cpu
local notation "load₂" i:arg tick:arg => (v₂ i tick).archivePhase (cursor i).floor ((menu).profile i) w


local notation "walk₀" z => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z


local notation "bare_" i:arg tick:arg => (OrdinaryBooks.atDate G S op g k i p frozen drift degree payload
  ((menu).seats i) (cursor i).ports).onTicket tick g frozen p f payload ((menu).seats i)
    (cursor i).ports.venue.lanes (cursor i).ports.io.roster (menu).ordinary
local notation "atFloor" i:arg tick:arg => (bare_ i tick).stageStart (cursor i).floor
local notation "actEntry" i:arg tick:arg => (bare_ i tick).registeredEntry (cursor i).ports (atFloor i tick)
local notation "actMatch" i:arg tick:arg => (bare_ i tick).registered_match (cursor i).ports (atFloor i tick)
  (Nat.le_max_left (cursor i).ports.argumentsPerNode (S.retainedArgumentsAt G drift))

theorem accepted_venue_with_rooms (protected_ : ∀j,RegisterTimeline.Protected (cpu j) (cursor j).floor header)
    (beforeHeader : lo+extent pitch (ch).layout≤header) (lower : header< initial.floor)
    (votes : (ch).Pin→Bool) (m : Memory w)
    (original : ∀a∈shelves pitch lo 0 (ch).layout,∀j:Fin (slots a.src.seats pitch),
      m (a.base+j.val)=((packed a.src.pin votes pitch j.val).val:Computability.VPVNP.BurstRAM.Word w))
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

    (families:0<S.baseGroups)
    (purchased:Branch.PositiveVenueRooms (X:=X) (G:=G) (S:=S) ticket op frozen drift degree payload (cursor i).floor (cursor i).ports
      (menu).ordinary (menu).seats w codeRoom) :
    DatePorts.returnedVenue (cursor i).ports ticket op g frozen p f drift degree payload ((menu).seats i)
      (cursor i).floor (menu).ordinary w ((menu).profile i) header prior.placement.fieldBits codeRoom exec (liveCPU m i):=by
  obtain ⟨a,b,c,ledger⟩:=purchased.funded
  exact accepted_registered_venue X G S ordinary reset branch positive room shorten w fit board op frozen drift
    degree payload lo header initial protected_ beforeHeader lower votes m original ticket before after located
    accepted codeRoom exec cells old height age floorFit keys counts grainRoom layoutRoom families
    purchased.inlet purchased.gather purchased.origin purchased.reach purchased.signed ledger

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
