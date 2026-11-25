import OAI.Hierarchy.DescentNamedPrimitiveCharge
import OAI.Hierarchy.DescentNamedOrdinaryEntryRoom
import OAI.Hierarchy.DescentRegisteredSignedSpace
import OAI.Hierarchy.DescentNamedMaterialRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryPeerRoom
import OAI.Hierarchy.DescentNamedOrdinaryExecution

namespace OAI
/-! # The selected ordinary instruction runs on arbitrary memory at the purchased addresses -/
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
local notation:max "codeRoom" w:arg => DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary w
local notation:max "fullRoom" w:arg sh:arg a:arg ok:arg => DatePorts.OrdinaryExecutionRoom ports ticket op g frozen p f drift degree payload
  (atSeats i) root ordinary w sh a ok

include before tail cut in
/-- The selected source program is total on malformed memory too. The source
profile, primitive-width invoice and signed aperture use their public dated budgets. -/
theorem selected_execution_room (w shelf address ratio:ℕ)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (funded:MatcherRoom G S k p payload) (word:payload≤w) (size:w≤ratio*payload)
    (hk:0<k) (ready:2*(signed₀).unit≤payload) (lanes:0<(modelAt).vector.lanes)
    (ordered:address≤root)
    (external_:(sourceBank shelf (modelAt).profileRepack.seats (modelAt).profileRepack.oldLanes).Fits w root)
    (guard:(modelAt).signedGuard start<2^w) (limit:(modelAt).fullEnd root<2^w)
    (primitive:(selectedEntry).Room (modelAt) start w → (modelAt).PrimitiveRoom start selectedEntry w)
    (ok:codeRoom w):fullRoom w shelf address ok:=by
  obtain ⟨matchRoom,entryRoom⟩:=selected_entry_room X G S br ticket before tail cut op frozen drift degree
    payload root ports ordinary board atSeats prices headerBase w word cells matcher funded limit guard
  have measuredRoom : (modelAt).area.Space ports.io w start := by
    rw [(ordinary_reel_layout X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
      root ports ordinary).1]
    exact matchRoom
  have signed:=(registered_signed_room X G S br ticket before tail cut op frozen drift degree payload
    (atSeats i) root ports ordinary w hk (funded.hosts i) ready measuredRoom guard)
  have material:=selected_material_room X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary word signed.1
  have peers:=DatePorts.ordinary_peer_room ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary
    cells.room.header signed.1
  have orig:=(issued_return_fields X G S br ticket before tail cut liveBooks frozen payload (atSeats i)
    ports.venue.lanes ports.io.roster ordinary).2.2.2
  have trueShape:(modelAt).signedLayout.format (modelAt).payload=(modelAt).signed:=
    congrArg (fun a=>PhysicalOrdinary.signed a) orig
  have named:(modelAt).withIssuedSigned=(modelAt):=by
    unfold PhysicalOrdinary.withIssuedSigned
    rw [trueShape]
  have marks:=(modelAt).mark_room_of_signed start ports.io measuredRoom signed.1 named radix
  have age:i<S.length:=ticket.hubRows.choose
  have all_:=registered_result_resources X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary w ok signed.2 material peers marks signed.1 entryRoom cells.room.population.groups age lanes (primitive entryRoom)
  have shift:root ≤ start:=by
    change root≤(raw).profileRepack.endAddress root
    rw [(raw).profileRepack.translate];exact Nat.le_add_right ..
  have enough:start≤rot:=by
    have translated:=(match₁).rotation_add ports.io.roster 0 start
    simp only [Nat.add_zero] at translated
    rw [translated];exact Nat.le_add_right ..
  exact registered_execution_room X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary w shelf address ok ratio size external_ matchRoom (ordered.trans (shift.trans enough)) all_ limit

include before tail cut in
theorem calibrated_execution_room (w shelf address ratio:ℕ)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (funded:MatcherRoom G S k p payload) (word:payload≤w) (size:w≤ratio*payload)
    (hk:0<k) (ready:2*(signed₀).unit≤payload) (lanes:0<(modelAt).vector.lanes)
    (ordered:address≤root)
    (external_:(sourceBank shelf (modelAt).profileRepack.seats (modelAt).profileRepack.oldLanes).Fits w root)
    (guard:(modelAt).signedGuard start<2^w) (limit:(modelAt).fullEnd root<2^w)
    {t reset τ β copies driftR degreeMax:ℕ}
    (grant:ArgumentCalendar G op t f g reset τ β drift driftR degreeMax payload)
    (charge:OrdinaryBooks.PrimitiveCalendar G op t f g reset τ β drift degreeMax driftR payload)
    (schedule:S=stageNumbers G t (Nat.log 2 payload/(2*β)) f g reset copies frozen)
    (power:k=groupBits t (Nat.log 2 payload/(2*β)) (hostRate t reset) (capRate G t g) (cutRate t f g))
    (tailBits:frozen=TerminalScale.tail τ (Nat.log 2 payload/(2*β)))
    (growth:drift+1 ≤ scale (Nat.log 2 payload/(2*β)) driftR) (deg:degree≤degreeMax)
    (bin sockets:ℕ) (nonempty:0<sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^(S.rounds*S.height)*G.b))*bin)))) (hp:0<p)
    : ∃ok:codeRoom w,fullRoom w shelf address ok:=by
  have ok:=registered_geometry_fits X G S br ticket before tail cut op frozen drift degree payload root ports ordinary
    board atSeats prices headerBase w ticket.hubRows.choose word cells cells.degree matcher lanes limit
  refine ⟨ok,?_⟩
  apply selected_execution_room X G S br ticket before tail cut op frozen drift degree payload root ports ordinary
    board atSeats prices headerBase w shelf address ratio cells matcher funded word size hk ready lanes ordered external_ guard limit _ ok
  intro inlet
  have bound:(modelAt).primitiveRoof ((modelAt).operandEnd start)≤(modelAt).fullEnd root:=by
    change (modelAt).primitiveEnd start≤(modelAt).returnedEnd start
    unfold PhysicalOrdinary.returnedEnd DescentOrdinaryCountScan.endAddress DescentOrdinaryCountScan.out
    exact ((Nat.le_add_right _ (2^(modelAt).countBits)).trans (Nat.le_add_right _ (modelAt).area.batch)).trans (Nat.le_succ _)
  exact (selected_primitive_room X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    ports.venue.lanes ports ports.io.roster ordinary start grant charge schedule power tailBits growth deg bin sockets nonempty
    split hp cells.room.archive cells.room.args ticket.hubRows.choose inlet (bound.trans_lt limit)).1

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
