import OAI.Hierarchy.DescentDatedSignedSpace
import OAI.Hierarchy.DescentMatcherRoomCalendar
import OAI.Hierarchy.DescentRegisteredMatcherSpace
import OAI.Hierarchy.DescentRegisteredClipRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentRegisteredClipRoom
import OAI.Hierarchy.DescentDatedPhysicalObservation

namespace OAI
/-! # The reached original venue in the physical matcher's incoming coordinates -/
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

include before tail cut in
/-- Incoming register geometry purchases the true matcher and argument reads;
raw memory contents play no role in these address tests. -/
theorem selected_entry_room (w:ℕ) (ws:payload≤w)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (paid:MatcherRoom G S k p payload)
    (limit:(modelAt).fullEnd root<2^w) (guard:(modelAt).signedGuard start<2^w):
    (match₁).Space ports.io w start ∧ (selectedEntry).Room (modelAt) start w:=by
  let event:br.path.Event i:=.ordinary before ticket tail cut
  have kind:((kindCalendar S.rounds S.height).drop i).head?=some false:=by
    rw [←br.kinds];exact event.shown
  have age:i<S.length:=ticket.hubRows.choose
  have regular:=(ordinary_slot_factor G.b S.rounds g S.height i kind).1
  have degAt:=(ordinary_slot_degree G.b S.rounds g S.height i G.base_pos kind).1
  have degreeRead:ports.venue.degree=(d₀).degree:=cells.degree.trans degAt.symm
  obtain ⟨e,initial⟩:=cells.room.initialSites
  have oldH:ports.venue.hosts=hostRows (S.hostSize i):=cells.room.hosts.trans
    (NativePitch.hostRows_at_date initial radix i).symm
  have pitch:ports.venue.lanes=DescentSIMDLookup.lanes payload (d₀).amount:=by
    calc
      ports.venue.lanes=NativePitch.incoming S k frozen p f payload ordinary i:=cells.format.pitch age
      _=(ordinary i).lanesAt:=by simp only [NativePitch.incoming,ite_eq_left age,ite_eq_right (Nat.ne_of_lt regular)]
      _=_:=by rw [Ordinary.lanesAt,matcher.1,matcher.2]
  have clip:=registered_clip_room X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary w ws cells.room.header cells.room.actors oldH cells.room.population.groups degreeRead pitch limit
  have inlet:=registered_inlet X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary w ws clip cells.archive limit
  refine ⟨?_,inlet.1⟩
  have begin_:root ≤ start:=by
    change root≤(raw).profileRepack.endAddress root
    rw [(raw).profileRepack.translate];exact Nat.le_add_right ..
  have meter:=ordinary_meter_roof X G S br ticket before tail cut op frozen drift degree payload (atSeats i)
    root ports ordinary headerBase
  have deposit:rot≤(modelAt).donorEnd start:=meter.1.trans (meter.2.1.le.trans meter.2.2)
  have capFit:ports.venue.cap=(d₀).cap:=cells.capacity
  have amount:2*(d₀).amount≤payload:=by
    rw [←donor_date_eq X G S br ticket before tail cut];exact (paid.packed ticket).2
  have charge:=guard
  unfold PhysicalOrdinary.signedGuard at charge
  rw [(modelAt).signed_extent] at charge
  have last:rot<2^w:=by omega
  exact DatePorts.matcher_placement ports (d₀) payload (atSeats i) (S.censusBits p) w root start
    cells.room.wires cells.room.ports cells.room.header cells.room.actors cells.room.paid begin_
    cells.format.width degreeRead capFit oldH cells.room.population.groups pitch
    (DonorDate.dated_cap_pos ..) paid.census (Nat.two_pow_pos _) amount ws last

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
