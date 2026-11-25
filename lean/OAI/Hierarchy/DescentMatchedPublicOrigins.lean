import OAI.Hierarchy.DescentMatchedPublicActor
import OAI.Hierarchy.DescentPublicRowsOfOrigins

namespace OAI
/-! Public operand origins on the particular actor memory reached by the scheduled reset. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
open scoped Fin.CommRing
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
variable (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀ (S.firstWidth G.b p) (S.grainAt G.b p 0)
      cursor.ports.operandLanes cursor.ports.roleLanes cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w
      (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
local notation "pre" => (a).ingress.phase base w (io).hubs (fun x=>(io).atoms x.val) (fun j=>(io).wire j.1.val j.2.val)
local notation "atMem" m:arg => (pre).image ((publisher).image m)
include B in
abbrev MatchedPublicOriginsAt (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready) (m : Memory w) (capAt : input.placement.cap=cap) (dst : Memory w) : Prop :=by
  let entry := (publisher).image m
  let q := rcut
  let previous := oldExp
  let pitch := nextM
  let printed := token
  have thisCut := fits
  have oldCut := priorFits
  subst n
  subst h
  subst f
  subst g
  subst tail
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  exact ∃μ measured,DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload q previous (2^q) pitch oldL roleL printed old io base w
      thisCut thisCut oldCut (history).count (history).nodeBase (history).arguments (history).seed
      (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) degreeAt ready entry capAt μ measured dst

include B in
abbrev MatchedPublicOrigins (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D)
    (ready : (u).Ready) (m : Memory w) (capAt : input.placement.cap=cap) : Prop :=
  ∃dst : Memory w,(u).ThroughActors (atMem m) dst ∧
    MatchedPublicOriginsAt board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt dst

theorem matched_public_rows_of_origins (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (capAt : input.placement.cap=cap)
    (orig : MatchedPublicOrigins board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt) :
    MatchedPublicRows board₀ op₀ B p drift degree payload w ordinary cursor space hn hh hf hg ht hb ho ready m:=by
  let cutAtDate := rcut
  let previousExponent := oldExp
  let nextPitch := nextM
  let tokenBits := token
  have cutFits := fits
  have previousFits := priorFits
  let entryMemory := (publisher).image m
  obtain ⟨dst,chronological,rows⟩:=orig
  subst n
  subst h
  subst f
  subst g
  subst tail
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  obtain ⟨μ,measured,packets⟩:=rows
  exact ⟨dst,chronological,DateInputs.public_rows_of_origins (B:=B) drift degree payload cutAtDate previousExponent
    (2^cutAtDate) nextPitch oldL roleL tokenBits old io base w cutFits cutFits previousFits (history).count
    (history).nodeBase (history).arguments (history).seed (NamedCodeRoom.prepared space)
    (NamedCodeRoom.scene space) degreeAt ready entryMemory capAt packets⟩

variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)

local notation "finish" => FinalInputs.fromArchive G S board k tail age p f g drift degree payload rcut oldExp (2^rcut)
  nextM (op).C (op).w oldL roleL token old io base w fits fits priorFits (history).count
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) history s₀ Z₀ op capacity
variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
variable (paid : B.Recorded p)
include paid capacity geo in
theorem matched_public_actor_origins (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
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
    (boardRoom : h≤2^k) (elapsed : 0<age) (sorted : SourceSorted W input.order)
    (positive : 0<HH) : MatchedPublicOrigins board₀ op₀ B p drift degree payload w ordinary cursor space
      hn hh hf hg ht hb ho degreeAt ready m capAt:=by
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
  cases (eq_of_heq hb : ctl.board=board₀)
  cases ho
  obtain ⟨μ,measured,dst,rows⟩:=DateInputs.fromNamed_public_origins_at (B:=B) paid drift degree payload cutAtDate previousExponent (2^cutAtDate)
    nextPitch oldL roleL tokenBits old io base w cutFits cutFits previousFits (history).count
    (history).nodeBase (history).arguments (history).seed (NamedCodeRoom.prepared space)
    (NamedCodeRoom.scene space) degreeAt ready entryMemory gr fee capAt historyAt branch
    seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit namesFit
    degFit laneRoom hubSpan capacity pitchOld rfl rfl narrow word ceiling geo.format.width geo.room.hosts boardRoom
    elapsed sorted finalInputs positive
  exact ⟨dst,(DateInputs.classified_prefix ready rows.2.1 rows.2.2.1).1,μ,measured,rows⟩
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
