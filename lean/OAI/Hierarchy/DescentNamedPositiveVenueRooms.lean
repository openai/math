import OAI.Hierarchy.DescentRegisteredPositivePitch
import OAI.Hierarchy.DescentNamedPrimitiveCharge
import OAI.Hierarchy.DescentNamedOrdinaryEntryRoom
import OAI.Hierarchy.DescentRegisteredSignedSpace
import OAI.Hierarchy.DescentNamedMaterialRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryPeerRoom
import OAI.Hierarchy.DescentNamedOrdinaryExecution

namespace OAI
/-! # The native banks used by the selected ordinary transition -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM DescentSIMDLookup DescentOrdinaryVenueIngress
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
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "cap₀" => Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift)
local notation "m₀" => (base).registered_match ports ((base).stageStart root) cap₀
local notation "stage" => (v).stageStart root
variable {bn bd : ℕ} (board : NonlinearExpanders.Graph bn bd) (atSeats prices : ℕ→ℕ) (headerBase:ℕ)
local notation "menu₀" => (⟨board,op,g,frozen,p,f,drift,degree,payload,atSeats,ordinary,prices,headerBase⟩:RegisterTimeline.Menu bn bd)

local notation "modelAt" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary


open DescentColonies Computability.VPVNP.BurstRAM PrivateRAM


local notation "liveBooks" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload (atSeats i) ports
local notation "raw" => (liveBooks).onTicket ticket g frozen p f payload (atSeats i) ports.venue.lanes ports.io.roster ordinary
local notation "start" => (raw).stageStart root
local notation "selectedEntry" => (raw).registeredEntry ports start
local notation "match₁" => (d₀).schedule payload (atSeats i) (S.censusBits p)
local notation "rot" => (match₁).rotationEnd ports.io.roster start


open DescentPacking.PackedMatch.Local.Stage DescentPackedProfileInstall
local notation "signed₀" => SignedStage.atDate G S g k i (NativePitch.incomingHosts S (i+1))
local notation "codeRoom" w => DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary w
local notation "fullRoom" w sh a ok => DatePorts.OrdinaryExecutionRoom ports ticket op g frozen p f drift degree payload
  (atSeats i) root ordinary w sh a ok


local notation "matchEntry" => (raw).registered_match ports start
  (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

/-- Physical resources for reading the selected board and publishing the next venue. -/
structure PositiveVenueRooms (w:ℕ) (code:codeRoom w) : Prop where
  inlet : (selectedEntry).Room (modelAt) start w
  gather : ((selectedEntry).directory (modelAt) start matchEntry).refs.Room w ((modelAt).vectorStart start)
  origin : (modelAt).TicketAdmission start w code.signed (selectedEntry) matchEntry
    (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩ : Fin (7*(modelAt).vector.operands))
  reach : (modelAt).preparedUntil start<2^w
  signed : (modelAt).SignedRoom start w
  funded : ∃a b c:ℕ,(modelAt).FundedCaps payload a b c

variable {t reset τ β copies driftR degreeMax ratio:ℕ}
local notation "J" => Nat.log 2 payload/(2*β)
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g reset).choose
local notation "funds" => 44*argumentDigitRate G t f g reset driftR baseRate

include before tail cut in
theorem registered_positive_venue_rooms (w:ℕ) (code:codeRoom w)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (funded:MatcherRoom G S k p payload) (word:payload≤w)
    (hk:0<k) (ready:2*(signed₀).unit≤payload) (lanes:0<(modelAt).vector.lanes)
    (guard:(modelAt).signedGuard start<2^w) (limit:(modelAt).fullEnd root<2^w)
    (purchase:ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (returns:ReturnCalendar G t f g reset driftR funds τ β ratio payload)
    (schedule:S=stageNumbers G t J f g reset copies frozen)
    (depth:k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (cutoff:frozen=TerminalScale.tail τ J) (dr:drift+1 ≤ scale J driftR)
    (dg:degree≤degreeMax) (digits:p≤payload) (firstWidth:S.firstWidth G.b p≤payload) (live:0<p) :
    PositiveVenueRooms (X:=X) (G:=G) (S:=S) ticket op frozen drift degree payload root ports ordinary atSeats w code:=by
  obtain ⟨space,inlet⟩:=selected_entry_room X G S br ticket before tail cut op frozen drift degree payload root ports ordinary
    board atSeats prices headerBase w word cells matcher funded limit guard
  have date := donor_date_eq X G S br ticket before tail cut
  have issuedFields := issued_return_fields X G S br ticket before tail cut liveBooks frozen payload
    (atSeats i) ports.venue.lanes ports.io.roster ordinary
  have area : (modelAt).area = (d₀).schedule payload (atSeats i) (S.censusBits p) := by
    rw [← date]
    change ticket.ordinaryArea (Nat.clog 2 (S.hostSize i)) (S.censusBits p) payload
      (raw).unit (DescentTerminalEpochBits.width G.C) (atSeats i) = _
    rw [issuedFields.2.1]
    rfl
  have modelSpace : (modelAt).area.Space ports.io w start := area.symm ▸ space
  have signed:=(registered_signed_room X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) root ports ordinary w hk (funded.hosts i) ready modelSpace guard).1
  have high:=((raw).registered_prepared_limit ports start).trans_lt code.endFit
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=(modelAt).ticket_source_order start
  have middle:=r₇.trans (r₈.trans r₉)
  have low:=r₁.trans_lt (r₂.trans_lt (r₃.trans_lt (r₄.trans_lt (r₅.trans_lt (r₆.trans_lt (middle.trans_lt high))))))
  have heads:=(modelAt).signed_ticket_head_room start code.signed signed (middle.trans_lt high)
  have gather:=DatePorts.ordinary_gather_room ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary
    inlet cells.room.population.groups lanes low
  have origin:=cut_ticket_admission X G S br ticket before tail cut ports op frozen drift degree payload (atSeats i) root ordinary
    code.signed (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(modelAt).vector.operands))
    inlet cells.room.population.groups ticket.hubRows.choose lanes low heads.1 heads.2
  have baseWidth:=registered_base_width X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) ports.venue.lanes ports ports.io.roster ordinary purchase schedule depth digits
  have money:=registered_row_funding X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) ports.venue.lanes ports ports.io.roster ordinary start purchase returns schedule depth cutoff dr baseWidth
    dg digits firstWidth cells.room.archive cells.room.args live
  exact ⟨inlet,gather,origin,high,signed,_,_,_,money.1⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
