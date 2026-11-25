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
set_option maxHeartbeats 500000
set_option quotPrecheck false

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


open DescentColonies Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

include before tail cut in
theorem registered_incoming_venue (w : ℕ) (m : Memory w) (age : i< S.length)
    (cells : RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (matcher : (ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (old : ports.held prior root m) :
    ∃hv:Fintype.card prior.V≤2^(modelAt).level,
      stageVenue prior hv ports.io (modelAt).area.lanesAt (modelAt).bitsPerField root (prior.venueRoster hv) m ∧
      (∀x:Block k,∀j:Fin (2*prior.placement.cap),(ports.io.wire x.val j.val).base+
        2^(modelAt).level*DescentSIMDLookup.chunks (S.groupCount i) (modelAt).area.lanesAt≤ root) ∧
      m ports.archive.count.base=(Fintype.card prior.V : Computability.VPVNP.BurstRAM.Word w):=by
  let event:br.path.Event i:=.ordinary before ticket tail cut
  have hit:((kindCalendar S.rounds S.height).drop i).head?=some false:=by rw [←br.kinds];exact event.shown
  have regular:=(ordinary_slot_factor G.b S.rounds g S.height i hit).1
  obtain ⟨n,home⟩:=cells.room.initialSites
  have H : ports.venue.hosts=2^(modelAt).level:=cells.room.hosts.trans (NativePitch.hostRows_at_date home radix i).symm
  have lanes : ports.venue.lanes=(modelAt).area.lanesAt:=by
    have oldPitch:=cells.format.pitch age
    rw [NativePitch.incoming,ite_eq_left age,ite_eq_right (Nat.ne_of_lt regular)] at oldPitch
    calc
      ports.venue.lanes=(ordinary i).lanesAt:=oldPitch
      _=DescentSIMDLookup.lanes payload (d₀).amount:=by rw [Ordinary.lanesAt,matcher.1,matcher.2]
      _=(modelAt).area.lanesAt:=rfl
  have sameBits : ports.venue.paidBits=(modelAt).bitsPerField:=cells.format.paid
  have cap : prior.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256:=
    congrArg Ordinary.cap (ordinary_geometry X G S br ticket before tail cut 0 1 0 0 0 0)
  have cap_ : prior.placement.cap=ports.venue.cap:=cap.trans cells.capacity.symm
  obtain ⟨wide,seen,used⟩:=old
  let readoutWith (capacity_ rowPitch_ countWidth_ : ℕ) : Prop :=
    ∃ hv : Fintype.card prior.V ≤ capacity_,
      stageVenue prior hv ports.io rowPitch_ countWidth_ root (prior.venueRoster hv) m
  have oldHeld : readoutWith ports.venue.hosts ports.venue.lanes ports.venue.paidBits := ⟨wide, seen⟩
  have newHeld : readoutWith (2^(modelAt).level) (modelAt).area.lanesAt (modelAt).bitsPerField := by
    rw [←H, ←lanes, ←sameBits]
    exact oldHeld
  obtain ⟨wide_, seen_⟩ := newHeld
  refine ⟨wide_, seen_, ?_, used⟩
  · intro x j
    let oldX : Block ports.venue.k:=Fin.cast (congrArg (2^·) cells.format.width.symm) x
    let oldJ : Fin (2*ports.venue.cap):=Fin.cast (congrArg (2*·) cap_) j
    obtain ⟨within,rows⟩:=cells.room.wires oldX oldJ
    have size:=(Nat.add_le_add_left rows (ports.io.wire x.val j.val).base).trans within.2.2
    have groupCount : ports.venue.groups = S.groupCount i := cells.room.population.groups
    simpa only [H,groupCount,lanes] using size

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
