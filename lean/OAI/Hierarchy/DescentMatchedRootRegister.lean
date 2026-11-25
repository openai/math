import OAI.Hierarchy.DescentMatchedPublicOrigins
import OAI.Hierarchy.DescentNamedOriginalRegister

namespace OAI
/-! # Original root register at a scheduled reset -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
open scoped Classical Fin.CommRing
set_option hygiene false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n₁ h₁ C f₁ g₁ cut tail₁ wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n₁ h₁ C f₁ g₁ cut tail₁}
    {n h f g tail : ℕ} (board₀ : NonlinearExpanders.Graph n h) (op₀ : RotorSpec)
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => op₀
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => board₀
local notation "old" => cursor.ports.venue
local notation "io" => cursor.ports.io
local notation "cap" => ((capCalendar G.b S.rounds g S.height).take age).prod*256
local notation "oldExp" => NativePitch.resetCut S k tail p f payload age
local notation "nextM" => NativePitch.incoming S k tail p f payload ordinary (age+1)
local notation "oldL" => cursor.ports.operandLanes
local notation "roleL" => cursor.ports.roleLanes
local notation "token" => DescentPrimitivePalette.printedBits G s₀ Z₀ op
local notation "rcut" => receiverCut G S board k tail age p f g drift degree payload oldExp nextM (op).C (op).w
  oldL roleL token old
local notation "base" => cursor.ports.priorStart k cursor.floor
local notation "history" => (cursor.ports.afterPad k cursor.floor).archive
local notation "outer" => scheduledAtPorts G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor
local notation "a" => (outer).inner
local notation "v" => (a).successor
local notation "start" => (a).stageStart base
local notation "E" => (a).estimator start
local notation "HH" => S.hostSize age
local notation "Ht" => GroupStage.depthBound (old).degree n f g
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap
local notation "fits" => scheduled_cut_origin G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL old
local notation "priorFits" => preceding_cut S k tail p f payload age
local notation "menu" => (⟨board,op,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h)
local notation "publisher" => priorArchivePhase G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w
variable (capacity : (old).cap=cap)
    (space : ScheduledCodeRoom G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ oldL roleL
      old io base w history)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "finish" => FinalInputs.fromArchive G S board k tail age p f g drift degree payload rcut oldExp (2^rcut)
  nextM (op).C (op).w oldL roleL token old io base w fits fits priorFits (history).count
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) history s₀ Z₀ op capacity
local notation "ports" => cursor.ports
variable (geo : Geometry G S menu k w age cursor)
variable (paid : B.Recorded p)
local notation "pre" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val) (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (pre).image ((publisher).image m)
open DescentPrimitivePalette DescentKernelHistory DescentLocalArchiveOrder
include paid capacity in
/-- Reservation and order are taken from the stencil run that supplied this
actor's saved root packet.  The final selector reads that same reset's class state. -/
theorem matched_root_register (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (capAt : input.placement.cap=cap) (historyAt : hist=S.firstWidth G.b p) (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host (io) (v).funded.oldLanes (v).funded.precision base
      (input.venueRoster input.valid.host) ((publisher).image m)) (popFit : (history).count.Fits w base)
    (popRead : (publisher).image m (history).count.base=(Fintype.card input.V:Computability.VPVNP.BurstRAM.Word w))
    (wireRoom : ∀(x:DescentColonies.Block k)(j:Fin (2*input.placement.cap)),(cursor.ports.io.wire x.val j.val).Fits w base ∧
      HH*chunks (S.groupCount age) (v).funded.oldLanes≤(cursor.ports.io.wire x.val j.val).size)
    (oldPos : 0<(v).funded.oldLanes) (oldWidth : (v).funded.precision=S.censusBits p)
    (entryFits : start<2^w) (low : k≤(E).low)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (live : 0 < amp) (degreePos : 0 < 32*Nat.clog 2 (2*cursor.ports.venue.degree))
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p) ≤ w) (hostBits : HH < 2^w)
    (ranksFit : cursor.ports.venue.degree*2^Ht < 2^w)
    (namesFit : DescentFallbackShapeTable.actorWordBits k (32*Nat.clog 2 (2*cursor.ports.venue.degree)) g n ≤ w)
    (degFit : cursor.ports.venue.degree+1 < 2^w) (laneRoom : 2^rcut ≤ w)
    (hubSpan : HH≤(io).hubs.size) (pitchOld : (old).lanes=2^oldExp)
    (narrow : 8*(v).groupWidth≤payload) (word : payload≤w) (ceiling : (outer).fullEnd<2^w)
    (elapsed : 0<age) (sorted : SourceSorted W input.order)
    [Fintype P] (whole : p∣B.reset.unit) (ar : Archive W) (ord : Local ar.bit)
    (safe : (finish).Room) (mid actorMem : Memory w)
    (spent : (u).throughOperandDate.Runs (atMem m) mid)
    (origins : MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt actorMem) :
    Nonempty (RootRegister B paid.positive whole ar ord (v).birth (finish).guards
      ((finish).classImage mid) rfl rfl rfl) :=by
  let cutAtDate := rcut
  let previousExponent := oldExp
  let nextPitch := nextM
  let tokenBits := token
  have cutFits := fits
  have previousFits := priorFits
  let entryMemory := (publisher).image m
  let finalInputs : (u).FinalInputs := finish
  subst n
  subst h
  subst f
  subst g
  subst tail
  have sameBoard : ctl.board=board₀:=eq_of_heq hb
  subst board₀
  subst op₀
  obtain ⟨basis,measured,_,_,_,_,reservation,order,counts,measuredRun,_⟩:=
    DateInputs.fromNamed_packet_entry paid drift degree payload cutAtDate previousExponent (2^cutAtDate)
      nextPitch oldL roleL tokenBits old io base w cutFits cutFits previousFits (history).count
      (history).nodeBase (history).arguments (history).seed (NamedCodeRoom.prepared space)
      (NamedCodeRoom.scene space) degreeAt ready entryMemory gr fee capAt historyAt branch seen popFit popRead
      wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit degFit
      laneRoom hubSpan capacity pitchOld rfl rfl narrow word ceiling
  obtain ⟨_,readAt,_,sourceRun,_,⟨hdr,raw,packetRead⟩,_⟩:=origins
  have same : measured=readAt:=ProtocolRAM.exec_unique _ _ _ _ measuredRun sourceRun
  subst readAt
  exact ⟨FinalInputs.fromNamed_original_register paid drift degree payload cutAtDate previousExponent
    (2^cutAtDate) nextPitch oldL roleL tokenBits old io base w cutFits cutFits previousFits (history).count
    (history).nodeBase (history).arguments (history).seed (NamedCodeRoom.prepared space)
    (NamedCodeRoom.scene space) degreeAt capAt finalInputs safe whole ar ord ready rfl rfl narrow word ceiling
    score measured basis reservation order counts popFit gr fee hostBits branch elapsed sorted live
    (by simpa only [input.branch, degreeAt] using degreePos) hdr raw packetRead measuredRun spent⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
