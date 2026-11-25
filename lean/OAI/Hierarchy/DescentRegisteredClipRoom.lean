import OAI.Hierarchy.DescentOrdinaryClipPathRoom
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentOrdinarySlotDegree
import OAI.Hierarchy.DescentRegisteredOrdinaryFits
import OAI.Hierarchy.DescentRegisteredDonorExtent
import OAI.Hierarchy.DescentDatePortActorRoom

namespace OAI
/-! # Admission of a registered ordinary program from its previous published banks -/
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
include before tail cut in
theorem registered_clip_room (w : ℕ) (word : payload≤w)
    (header : ports.HeaderRoom w root) (actors : ports.ActorRoom w root)
    (homes : ports.venue.hosts=hostRows (S.hostSize i)) (groups : ports.venue.groups=S.groupCount i)
    (degreeAt : ports.venue.degree=(d₀).degree)
    (pitch : ports.venue.lanes=DescentSIMDLookup.lanes payload (d₀).amount)
    (space : (v).fullEnd root<2^w) :
    (entry).clip.Room (entry).venue ((v).signedEnd stage) w:=by
  obtain ⟨_,quoted⟩:=registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  obtain ⟨stored,rows⟩:=registered_donor_extent X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have lower : root ≤ stage:=by
    change root≤(v).profileRepack.endAddress root
    rw [(v).profileRepack.translate]
    exact Nat.le_add_right ..
  have signed : root≤(v).signedEnd stage:=by
    rw [(v).signed_extent,(v).donor_shift]
    omega
  have refs : (v).refsStart stage≤(v).endAddress stage:=by
    obtain ⟨u₀,u₁⟩:=(v).mount_order stage
    obtain ⟨u₂,u₃,u₄,u₅,u₆⟩:=(v).routed_order stage
    omega
  have raster : (v).endAddress stage≤(v).rasterEnd stage:=by
    change _≤StageVenueTail.OrdinaryRaster.roof _ _ _ _
    rw [StageVenueTail.OrdinaryRaster.translated]
    exact Nat.le_add_right ..
  have endFit : (v).endAddress stage<2^w:=(raster.trans ((v).raster_below_full root)).trans_lt space
  have donor:=(v).signed_stage_paid stage
  have allocated : (entry).venue.panel.base+(entry).venue.panel.size≤(v).signedEnd stage:=
    stored.trans (donor.1.trans (donor.2.1.trans donor.2.2))
  obtain ⟨_,u₀,u₁,u₂,u₃⟩:=(entry).inlet_order (v) stage
  have fitsClip : (entry).clip.fullEnd ((v).signedEnd stage)<2^w:=
    ((u₀.trans (u₁.trans (u₂.trans u₃))).trans ((m₀).atRefs.le.trans refs)).trans_lt endFit
  have paths:=(entry).clip.paths_fit ((v).signedEnd stage) fitsClip
  have lowEnd:=((entry).clip.bounds ((v).signedEnd stage))
  have limit : (v).signedEnd stage<2^w:=(lowEnd.1.trans (lowEnd.2.1.trans lowEnd.2.2)).trans_lt fitsClip
  have panel : (entry).venue.panel.Fits w ((v).signedEnd stage):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (allocated.trans_lt limit),allocated⟩
  have grow {b:Bank} (fit:b.Fits w root) : b.Fits w ((v).signedEnd stage):=
    ⟨fit.1,fit.2.1,fit.2.2.trans signed⟩
  have h : (entry).clip.venue.hosts=ports.venue.hosts:=by rw [quoted,homes]; rfl
  have gr : (entry).clip.venue.groups=ports.venue.groups:=by rw [quoted,groups]; rfl
  have actorLane : (entry).clip.actorPitch=ports.venue.lanes:=by rw [quoted,pitch]; rfl
  have total : (entry).clip.venue.socket.degree=ports.venue.degree:=by rw [quoted,degreeAt]; rfl
  have many : 0<ports.venue.hosts:=by rw [homes]; exact Nat.two_pow_pos _
  refine ⟨?_,rows,?_,?_,?_,?_,?_,?_,paths,fitsClip⟩
  · intro B member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact panel
    · exact grow actors.fits
    · exact grow header.hubs
    · exact grow header.roster
  · rw [h,gr,actorLane]
    exact actors.rows
  · rw [h]
    exact header.hosts
  · rw [h,total]
    exact header.peers
  · rw [quoted]
    exact word
  · rw [h]
    exact header.hosts.trans_lt header.hubs.2.1
  · rw [total]
    exact ((Nat.le_mul_of_pos_left _ many).trans header.peers).trans_lt header.roster.2.1

include before tail cut in
theorem ordinary_fits (w : ℕ) (word : payload≤w)
    (header : ports.HeaderRoom w root) (actors : ports.ActorRoom w root)
    (homes : ports.venue.hosts=hostRows (S.hostSize i)) (groups : ports.venue.groups=S.groupCount i)
    (degreeAt : ports.venue.degree=(d₀).degree)
    (pitch : ports.venue.lanes=DescentSIMDLookup.lanes payload (d₀).amount)
    (space : (v).fullEnd root<2^w)
    (age : i<S.length) (positive : 0<(v).resolver.lanes) (archive : ports.ArchiveFits k root)
    (cash : ports.PaidRoom w root) :
    DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload seats root ordinary w:=
  registered_admission X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
    w age word positive
    (registered_clip_room X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
      w word header actors homes groups degreeAt pitch space) archive cash space

variable {bn bd : ℕ} (board : NonlinearExpanders.Graph bn bd) (atSeats prices : ℕ→ℕ) (headerBase:ℕ)
local notation "menu₀" => (⟨board,op,g,frozen,p,f,drift,degree,payload,atSeats,ordinary,prices,headerBase⟩:RegisterTimeline.Menu bn bd)

local notation "modelAt" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary

include before tail cut in
/-- The authentic predecessor geometry and the current public matcher profile
discharge the clipped donor, actor, roster and archive checks jointly. -/
theorem registered_geometry_fits (w:ℕ) (age:i<S.length) (word:payload≤w)
    (cells:RegisterTimeline.Geometry G S menu₀ k w i ⟨ports,root⟩)
    (priorDegree:ports.venue.degree=atRound (i%(S.rounds+1)))
    (matcher:(ordinary i).payload=payload ∧ (ordinary i).unit=(d₀).amount)
    (positive:0<(modelAt).resolver.lanes) (space:(modelAt).fullEnd root<2^w) :
    DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload (atSeats i) root ordinary w:=by
  let event : br.path.Event i:=.ordinary before ticket tail cut
  have kind : ((kindCalendar S.rounds S.height).drop i).head?=some false:=by
    rw [←br.kinds]
    exact event.shown
  have ordinaryDate:=(ordinary_slot_factor G.b S.rounds g S.height i kind).1
  have degreeAt:=(ordinary_slot_degree G.b S.rounds g S.height i G.base_pos kind).1
  have degree₀ : ports.venue.degree=(d₀).degree:=priorDegree.trans degreeAt.symm
  obtain ⟨exponent,initialSites⟩:=cells.room.initialSites
  have homes : ports.venue.hosts=hostRows (S.hostSize i):=cells.room.hosts.trans
    (NativePitch.hostRows_at_date initialSites radix i).symm
  have pitch:ports.venue.lanes=DescentSIMDLookup.lanes payload (d₀).amount:=by
    calc
      ports.venue.lanes=NativePitch.incoming S k frozen p f payload ordinary i:=cells.format.pitch age
      _=(ordinary i).lanesAt:=by simp only [NativePitch.incoming,ite_eq_left age,ite_eq_right (Nat.ne_of_lt ordinaryDate)]
      _=DescentSIMDLookup.lanes payload (d₀).amount:=by rw [Ordinary.lanesAt,matcher.1,matcher.2]
  exact ordinary_fits X G S br ticket before tail cut op frozen drift degree payload (atSeats i) root ports ordinary
    w word cells.room.header cells.room.actors homes cells.room.population.groups degree₀ pitch space age positive
    cells.archive cells.room.paid

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
