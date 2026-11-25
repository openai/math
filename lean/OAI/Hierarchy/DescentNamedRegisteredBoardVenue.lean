import OAI.Hierarchy.DescentRegisteredIncomingVenue
import OAI.Hierarchy.DescentRegisteredSelectedReturn
import OAI.Hierarchy.DescentNamedOrdinaryEntryRoom
import OAI.Hierarchy.DescentRegisteredDonorExtent
import OAI.Hierarchy.DescentNamedSignedReturn

namespace OAI
/-! # The original named ballot returns its successor register from the actual earlier held archive -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM DescentSIMDLookup DescentOrdinaryVenueIngress
noncomputable section
set_option quotPrecheck false

private abbrev admittedBoardPage {F I : Type} [Field F] (model : PhysicalOrdinary F I)
    (floor width : ℕ) (signed : model.SignedChart) (entry : model.ArgumentEntry)
    (match_ : entry.Match model floor) (slots : 0 < model.vector.operands) : Prop :=
  model.TicketAdmission floor width signed entry match_ ⟨0, Nat.mul_pos (by decide : 0 < 7) slots⟩

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
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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


open DescentColonies DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentGroupPeerOrder ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM


local notation "bare" => (OrdinaryBooks.atDate G S op g k i p frozen drift degree payload (atSeats i) ports).onTicket
  ticket g frozen p f payload (atSeats i) ports.venue.lanes ports.io.roster ordinary
local notation "start" => (bare).stageStart root
local notation "entryAt" => (bare).registeredEntry ports start
local notation "matching" => (bare).registered_match ports start (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "make" fn:arg => fn ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary
variable (w:ℕ)(pos:0<k)(code:DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary w)
  (exec:DatePorts.OrdinaryExecutionRoom ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary w (prices i) headerBase code)
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(modelAt).vector.operands))
local notation "funds" m:arg => (make DatePorts.ordinaryDonorMemory) w (prices i) headerBase pos code exec m

set_option maxHeartbeats 2400000 in
include before tail cut in
theorem registered_board_venue (m:Memory w)(age:i<S.length)(height:0<S.height)(gain:G.b≤2^S.capGain)(families:0<S.baseGroups)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (old:ports.held prior root m)
    (board_ : ∃(wide:Fintype.card prior.V≤(modelAt).area.H)(pick:(prior.placement.stage.result nonneg).Choice),
      HEq choice pick ∧ Nonempty ((modelAt).SelectedBoard (w:=w) wide
        (hostRotor (GroupStage.plane (modelAt).hostNumbers wide)
          (hostRoster prior.placement ((GroupStage.plane (modelAt).hostNumbers wide).trans Fin.valEmbedding)))
        pick (funds m) (entryAt).venue.panel))
    (inlet:(entryAt).Room (modelAt) start w)
    (gather:((entryAt).directory (modelAt) start matching).refs.Room w ((modelAt).vectorStart start))
    (origin:admittedBoardPage (modelAt) start w code.signed (entryAt) matching code.slots)
    (reach:(modelAt).preparedUntil start<2^w)(cash:(modelAt).SignedRoom start w)
    {δ₀ δ₁ δ₂:ℕ}(ledger:(modelAt).FundedCaps payload δ₀ δ₁ δ₂):
    (make DatePorts.returnedVenue) w (prices i) headerBase pos code exec m:=by
  obtain ⟨wide,pick,chosen,⟨observed⟩⟩:=board_
  obtain ⟨_,source,oldWires,count⟩:=registered_incoming_venue X G S br ticket before tail cut op frozen drift degree
    payload root ports ordinary board atSeats prices headerBase w m age cells matcher old
  have returnedFields:=issued_return_fields X G S br ticket before tail cut
    (OrdinaryBooks.atDate G S op g k i p frozen drift degree payload (atSeats i) ports)
    frozen payload (atSeats i) ports.venue.lanes ports.io.roster ordinary
  have ⟨fixed,_⟩:=DatePorts.ordinary_registered_signed ports ticket op g frozen p f drift degree payload
    (atSeats i) root ordinary returnedFields.2.2.2
  have prevDegree:(modelAt).area.D=D:=prior.branch
  have nextDegree:=returnedFields.2.2.1.trans next.branch
  have previous:=registered_donor_extent X G S br ticket before tail cut op frozen drift degree payload (atSeats i) root ports ordinary
  let date:=DonorDate.atDate G S g k i p
  let menu:=(date.schedule payload (atSeats i) (S.censusBits p))
  have geom:(modelAt).area=menu:=
    (ordinary_reel_layout X G S br ticket before tail cut op frozen drift degree payload (atSeats i) root ports ordinary).1
  let rot:=menu.rotationEnd ports.io.roster start
  have first:root ≤ start:=by
    change root≤(bare).profileRepack.endAddress root
    rw [(bare).profileRepack.translate];exact Nat.le_add_right ..
  have next_:start≤rot:=by
    have e:=menu.rotation_add ports.io.roster 0 start
    simp only [Nat.add_zero] at e
    exact (Nat.le_add_right ..).trans_eq e.symm
  have rotated:=first.trans next_
  have charge:=ordinary_meter_roof X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary headerBase
  have floorPaid:=rotated.trans (charge.1.trans (charge.2.1.le.trans charge.2.2))
  have countAt:ports.archive.count.base<root:=
    (Nat.lt_add_of_pos_right (Nat.two_pow_pos ports.archive.count.bits)).trans_le cells.room.header.count.2.2
  obtain ⟨a,initial⟩:=cells.room.initialSites
  have hosts:0<(modelAt).venue.hosts:=by
    change 0<NativePitch.incomingHosts S (i+1)
    rw [NativePitch.incomingHosts_eq initial radix _ age]
    unfold AtomSchedule.hostSize
    rw [initial,radix];positivity
  have groups:0<S.groupCount (i+1):=by unfold AtomSchedule.groupCount;rw [radix];positivity
  have rows:0<chunks (S.groupCount (i+1)) (modelAt).venue.paidLanes:=by
    have q:=ThreeFlat.Routing.CallPool.count_le_batches_mul (S.groupCount (i+1)) (modelAt).venue.paidLanes ledger.out
    by_contra! negative
    have e:chunks (S.groupCount (i+1)) (modelAt).venue.paidLanes=0:=Nat.eq_zero_of_le_zero negative
    change _≤(modelAt).venue.paidLanes*chunks (S.groupCount (i+1)) (modelAt).venue.paidLanes at q
    rw [e,Nat.mul_zero] at q;omega
  have priceFit:=(prior.placement.census_caps_at S prior.valid height age.le
    (ticket.quantum.symm.trans (ticket.grain_on_cut before tail cut br.issuedGrains)) prior.edges gain).2
  apply DatePorts.returned_on_board ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary
    w (prices i) headerBase pos code exec m wide pick observed chosen.symm age radix source oldWires count countAt
    rotated floorPaid previous.1 prevDegree nextDegree inlet gather origin reach priceFit ledger.positive
    ledger.clipped ledger.out cash.lanes hosts rows fixed cash (geom.symm ▸ exec.matcher)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
