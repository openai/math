import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentRegisteredReturnedVenue
import OAI.Hierarchy.DescentDyadicHostDates
import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentDonorCounterBetween

namespace OAI
/-! # Positive semantic readback for the reached, funded ordinary update -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 9000

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


variable (w shelf header:ℕ) (positive:0<k)
local notation:max "make" f₀:arg => f₀ ports ticket op g frozen p f drift degree payload seats root ordinary
variable (ok:(DatePorts.OrdinaryCodeRoom (prevWorld := prior) (next := next) ports ticket op g frozen p f drift degree payload seats root ordinary) w)
variable (exec:(DatePorts.OrdinaryExecutionRoom (prevWorld := prior) (next := next) ports ticket op g frozen p f drift degree payload seats root ordinary) w shelf header ok)
local notation "match₀" => (base).registered_match ports floor₁ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry ports floor₁
local notation "steps" => (v).issuedSteps root ports entry ok.signed w match₀ sh ok.blocks ok.paths ok.slots ok.chip ok.endFit ok.packed ok.radix ok.funded
local notation "input₁" => (v).signedInput floor₁ ok.signed
local notation "return₁" => (v).reachedSources floor₁
local notation "at₁" => (v).rasterEnd floor₁
local notation:max "moved" m:arg => (v).beforeReturn root shelf header ports.io ports.archive.count input₁ steps (d₀) positive exec m

include before tail cut in
/-- It suffices to read the output arrays of the actual funded venue. The
matched schedule fixes both host degrees and capacities, and its counter lies
below the later mutable cells. -/
theorem held_from_venue (m:Memory w) (old:ports.held prior root m)
    (pop:DatePorts.Population S ports i) (initialPow:∃a,S.initialSites=2^a)
    (venueK:ports.venue.k=k)
    (capacity:ports.venue.cap=((calendar).take i).prod*256)
    (banks:ports.WireRoom w root) (archive:ports.HeaderRoom w root)
    (issued:(DatePorts.returnedVenue (prevWorld := prior) (next := next) ports ticket op g frozen p f drift degree payload seats root ordinary) w shelf header positive ok exec m) :
    (DatePorts.ordinaryPorts (prevWorld := prior) (next := next) ports ticket op g frozen p f drift degree payload seats root ordinary).held next ((v).fullEnd root)
      ((DatePorts.ordinaryOutput (prevWorld := prior) (next := next) ports ticket op g frozen p f drift degree payload seats root ordinary) w shelf header positive ok exec m):=by
  obtain ⟨l,initialPow⟩:=initialPow
  have oldHosts:ports.venue.hosts=(v).area.H:=by
    change _=hostRows (S.hostSize i)
    exact (pop.venue_eq S initialPow radix).trans (NativePitch.hostRows_at_date initialPow radix i).symm
  have sourceCap:=congrArg Ordinary.cap (ordinary_geometry X G S br ticket before tail cut 0 1 0 0 0 0)
  change prior.placement.cap=((calendar).take i).prod*256 at sourceCap
  have prevCap:=capacity.trans sourceCap.symm
  have venue:=venue_date_eq X G S br ticket before tail cut frozen payload ports.venue.lanes ordinary
  have degreeRead:=congrArg StageVenueTail.Date.degree venue
  have widthRead:=congrArg StageVenueTail.Date.cap venue
  have ages:=tail.kinds_length
  have age:i+1≤S.length:=by omega
  have num:Fintype.card next.V≤(v).venue.hosts:=by
    change _≤NativePitch.incomingHosts S (i+1)
    rw [NativePitch.incomingHosts_eq initialPow radix _ age]
    exact next.valid.host
  refine DatePorts.ordinary_output_held ports ticket op g frozen p f drift degree payload seats root ordinary
    w shelf header positive ok exec m old oldHosts ?_ ?_ ?_ ?_ num widthRead ?_ (issued num).1
  · intro x j
    let xx:=Fin.cast (congrArg (2^·) venueK.symm) x
    let jj:=Fin.cast (congrArg (2*·) prevCap.symm) j
    have paid:=banks xx jj
    have edges:=Nat.add_le_add_left paid.2 (ports.io.wire x.val j.val).base
    exact (by simpa only [oldHosts,pop.groups,xx,jj,Fin.val_cast] using edges.trans paid.1.2.2)
  · have size:=archive.count.1
    have endAddress:=archive.count.2.2
    omega
  · exact prior.branch
  · exact degreeRead.symm.trans next.branch
  · exact ordinary_meter_roof X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary header

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
