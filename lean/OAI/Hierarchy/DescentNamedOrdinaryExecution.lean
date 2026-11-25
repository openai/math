import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentRegisteredMatcherSpace
import OAI.Hierarchy.DescentRegisteredOrdinaryExecution
import OAI.Hierarchy.DescentMatchedReadRoom
import OAI.Hierarchy.DescentNamedCutTicketAdmission
import OAI.Hierarchy.DescentDatedNativeTicketHeadRoom
import OAI.Hierarchy.DescentOrdinaryPreparedLimit
import OAI.Hierarchy.DescentRegisteredArgumentGatherRoom

namespace OAI
/-! Executing the registered ordinary date on any contents of the originally selected addresses. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
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
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "floor₁" => (v).stageStart root
local notation "level₁" => Nat.clog 2 (S.hostSize i)
local notation "bits₁" => S.censusBits p
local notation "prof" => DescentTerminalEpochBits.width G.C


local notation "rotation" => ((d₀).schedule payload seats bits₁).rotationEnd ports.io.roster floor₁


open DescentDatedAddressBook DescentSIMDLookup DescentPackedColony DescentPackedProfileInstall
local notation "plan₀" => (d₀).schedule payload seats bits₁
local notation "match_" => (base).registered_match ports floor₁ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry ports floor₁
variable (w shelf header : ℕ)
variable (ok:DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload seats root ordinary w)
local notation "book" => (v).reachedSources floor₁
local notation "st" => (v).issuedSteps root ports entry ok.signed w match_ sh ok.blocks ok.paths ok.slots ok.chip ok.endFit ok.packed ok.radix ok.funded
local notation "direct" => (v).signedInput floor₁ ok.signed
local notation "room₀" => DatePorts.OrdinaryExecutionRoom ports ticket op g frozen p f drift degree payload seats root ordinary w shelf header ok

include before tail cut in
theorem registered_execution_room (amountRatio:ℕ) (ratio:w≤amountRatio*payload)
    (shelfFit:(sourceBank shelf (v).profileRepack.seats (v).profileRepack.oldLanes).Fits w root)
    (matcher:(plan₀).Space ports.io w floor₁) (past:header≤rotation)
    (late:(v).ResultRuns floor₁ ports.io ports.archive.count direct st)
    (limit:(v).fullEnd root<2^w) : room₀ :=by
  have actual:=donor_date_eq X G S br ticket before tail cut
  have returnedFields:=issued_return_fields X G S br ticket before tail cut books frozen payload seats ports.venue.lanes ports.io.roster ordinary
  have a:(base).area=ticket.donorDate.schedule payload seats bits₁:=by
    change ticket.ordinaryArea level₁ bits₁ payload (base).unit prof seats=_
    rw [returnedFields.2.1]; rfl
  have schedule:(v).area=plan₀:=by rw [←actual];exact a
  have deposit:(v).donorEnd floor₁=ticket.wholeDonorEnd
      (max (k+3) (Nat.clog 2 ((A).degree+1))) prof (DescentCompiler.TerminalScale.hostRows (S.hostSize i)) payload rotation:=by
    change ticket.wholeDonorEnd (base).short prof (2^level₁) payload ((base).area.rotationEnd ports.io.roster floor₁)=_
    rw [returnedFields.1,a,actual]; rfl
  have between:=ordinary_meter_roof X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary header
  have tailSpace:=(v).before_span floor₁ ports.io ports.archive.count direct book st ok.result late
  have last:(v).primitiveEnd floor₁≤(v).fullEnd root:=by
    change (v).primitiveEnd floor₁ ≤ (v).primitiveEnd floor₁ + _ + _ + 1
    exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  have extent:ticket.wholeDonorEnd (max (k+3) (Nat.clog 2 ((A).degree+1))) prof
      (DescentCompiler.TerminalScale.hostRows (S.hostSize i)) payload rotation≤2^w:=by
    rw [←deposit];exact tailSpace.1.trans (last.trans limit.le)
  apply DatePorts.ordinary_execution ports ticket op g frozen p f drift degree payload seats root ordinary w shelf header ok
    schedule shelfFit matcher _ late (between.1.trans (between.2.1.le.trans (between.2.2.trans tailSpace.1))) limit
  exact issued_matcher_rooms X G S br ticket before tail cut payload seats bits₁ ports.io floor₁ w header amountRatio matcher past ratio extent


local notation "packedSlot" => (⟨0,Nat.mul_pos (by decide : 0<7) ok.slots⟩:Fin (7*(v).vector.operands))
local notation "sources" => (⟨ports.archive.count,ports.io.roster,ports.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "elapsed" => (v).donorEnd floor₁

include before tail cut in
theorem registered_result_resources
    (ranks:PriorHeader.Room (entry).venue.adjacency (v).area.H (v).signed.groups (v).signed.lanes (v).signed.degree elapsed w)
    (material:(v).MaterialRoom ((v).materialStart floor₁) (entry).venue.panel
      (PriorHeader.reverseRank (v).area.H (v).signed.groups (v).signed.lanes (v).signed.degree elapsed) w)
    (peers:DescentOrdinaryVenueReturn.Room sources ((v).materialEnd floor₁) (v).area.H (v).area.D (v).venue.hosts (v).venue.degree w)
    (mark:(v).MarkRoom floor₁ ports.io w) («wire»:(v).SignedRoom floor₁ w)
    (inlet:(entry).Room (v) floor₁ w) (previous:ports.venue.groups=S.groupCount i) (age:i<S.length)
    (lanes:0<(v).vector.lanes)
    (primitive:(v).PrimitiveRoom floor₁ entry w) :
    (v).ResultRuns floor₁ ports.io ports.archive.count direct st:=by
  have high:=( (base).registered_prepared_limit ports floor₁).trans_lt ok.endFit
  obtain ⟨r₁,r₂,r₃,r₄,r₅,r₆,r₇,r₈,r₉⟩:=(v).ticket_source_order floor₁
  have middle:=r₇.trans (r₈.trans r₉)
  have low:=r₁.trans_lt (r₂.trans_lt (r₃.trans_lt (r₄.trans_lt (r₅.trans_lt (r₆.trans_lt (middle.trans_lt high))))))
  have heads:=(v).signed_ticket_head_room floor₁ ok.signed «wire» (middle.trans_lt high)
  have gather:=DatePorts.ordinary_gather_room ports ticket op g frozen p f drift degree payload seats root ordinary
    inlet previous lanes low
  have orig:=cut_ticket_admission X G S br ticket before tail cut ports op frozen drift degree payload seats root ordinary
    ok.signed packedSlot inlet previous age lanes low heads.1 heads.2
  exact DatePorts.ordinary_result_runs ports ticket op g frozen p f drift degree payload seats root ordinary w ok
    ranks material peers mark «wire» inlet gather orig high primitive

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
