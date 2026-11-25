import OAI.Hierarchy.DescentNamedOperandPanels
import OAI.Hierarchy.DescentScheduledVenueOld
import OAI.Hierarchy.DescentScheduledResetRankOperands
import OAI.Hierarchy.DescentRegisteredGeometry

namespace OAI
/-! # The packed operand assay and its registered predecessor on one reset -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentPackedColony DescentBundleHistory DescentSIMDLookup DescentResetGates
open DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
open scoped Classical Fin.CommRing
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (p drift degree payload w : ℕ) (ordinary : ℕ→Dated.Ordinary)
    (seats profile : ℕ→ℕ) (header : ℕ) (cursor : Position)
local notation "op" => RotorSpec.ofRates ctl
local notation "s₀" => S.firstWidth G.b p
local notation "Z₀" => S.grainAt G.b p 0
local notation "board" => ctl.board
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
variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
    (space : ScheduledCodeRoom G S ctl.board k tail age p f g drift degree payload ordinary (RotorSpec.ofRates ctl) (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space

local notation "ports" => cursor.ports
local notation "mem₁" m:arg => (publisher).image m
local notation "oldLayout" => previousArchiveLayout G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ ports cursor.floor
local notation "scheduledOld" => ScheduledOldAt G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ ports cursor.floor w space input
local notation "layoutEq" widths:arg homes:arg groups:arg args:arg => scheduled_loaded G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ ports cursor.floor widths homes groups args
local notation "paddedValues" ds:arg rs:arg => padValues G S board k tail age p f g drift degree payload ordinary op s₀ Z₀ ports cursor.floor ds rs
local notation "panels" => DateInputs.OperandPanelsAt (B:=B) drift degree payload rcut oldExp (2^rcut) nextM oldL roleL token old io base w
  fits fits priorFits (history).count (history).nodeBase (history).arguments (history).seed
  (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space)
variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) (RotorSpec.ofRates ctl))

def RegisteredOperandPanels (m : Memory w) (degreeAt : (old).degree=D) (capAt : input.placement.cap=cap)
    (ready : (u).Ready) (homes : (old).hosts=HH) (blocks : (old).k=k)
    (groups : (old).groups=S.groupCount age) (widths : DatePorts.ArchiveWidths G S (RotorSpec.ofRates ctl) cursor.ports k tail p drift degree payload age)
    (args : (ports).argumentsPerNode=(if age=0 then 3*(s₀/p) else S.retainedArgumentsAt G drift)) : Prop :=
  ∃(data : (oldLayout).Values) (roles : Fin (2^k)→Fin (ports).operandHosts→Fin (old).groups→Cell ((ports).tokenBits*(ports).nodes)),
    scheduledOld m homes blocks groups widths args number bounds shape label data roles ∧
    panels degreeAt capAt ready (mem₁ m) (layoutEq widths homes groups args ▸ paddedValues data roles)

variable (paid : B.Recorded p) (geo : Geometry G S (⟨ctl.board,RotorSpec.ofRates ctl,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S (RotorSpec.ofRates ctl) cursor.ports k tail p drift degree payload age)
    {pointer : NodeOrder.All description→ℕ→Pointer}
    {flags : Fin (2^cursor.ports.venue.k)→Fin cursor.ports.nodes→Fin cursor.ports.operandHosts→Fin cursor.ports.venue.groups→ℕ}

include paid capacity in
theorem scheduled_operand_panels (degreeAt : (old).degree=D) (ready : (u).Ready)
    (m : Memory w) (incoming : (ports).held input cursor.floor m)
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
    (hubSpan : HH≤ (io).hubs.size) (pitchOld : (old).lanes=2^oldExp)
    (narrow : 8*(v).groupWidth≤payload) (word : payload≤w) (ceiling : (outer).fullEnd<2^w)
    (boardRoom : h≤2^k) (elapsed : 0<age) (sorted : SourceSorted W input.order)
    (operandPos : 0<oldL) (rolePos : 0<roleL) (newFit : S.hostSize (age+1)≤2^w)
    (sized : (ports).RoleRows) (actual : DatePorts.ArchiveRead ports input description number bounds shape op label pointer flags m) :
    RegisteredOperandPanels B p drift degree payload w ordinary cursor space number bounds shape label m
      degreeAt capAt ready geo.room.hosts geo.format.width geo.room.population.groups widths geo.arguments :=by
  have available : base<2^w:=(outer).stages.2.trans_lt ceiling
  have countRoom : (ports).archive.count.base<cursor.floor:=
    (Nat.lt_add_of_pos_right (Nat.two_pow_pos (ports).archive.count.bits)).trans_le geo.room.header.count.2.2
  obtain ⟨data,roles,oldRows⟩:=scheduled_venue_archive_witness G S board k tail age p f g drift degree payload ordinary op
    s₀ Z₀ ports cursor.floor w space input m incoming countRoom geo.room.wires
    geo.room.hosts geo.format.width (capacity.trans capAt.symm) geo.room.population.groups geo.archive available
    rolePos widths geo.arguments actual widths.token sized
  refine ⟨data,roles,oldRows,?_⟩
  exact DateInputs.fromNamed_operand_panels (B:=B) paid drift degree payload rcut oldExp (2^rcut) nextM oldL roleL
    token old io base w fits fits priorFits (history).count (history).nodeBase (history).arguments (history).seed
    (NamedCodeRoom.prepared space) (NamedCodeRoom.scene space) degreeAt ready (mem₁ m) gr fee capAt historyAt
    branch seen popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits
    ranksFit namesFit degFit laneRoom hubSpan capacity pitchOld rfl rfl narrow word ceiling geo.format.width
    geo.room.hosts boardRoom elapsed sorted operandPos newFit _ oldRows.2.2.2.2.2

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
