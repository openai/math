import OAI.Hierarchy.DescentScheduledArchivePanels

namespace OAI
/-! # Operand panels on the original board selected by the calendar -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentSixParty DescentCompiler
open DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh DescentSIMDLookup DescentResetGates
open DescentPackedColony DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks DescentPrimitivePalette
open DescentPackedZip DescentOrdinaryHostPad DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
open scoped Classical Fin.CommRing
set_option quotPrecheck false
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
variable (space : ScheduledCodeRoom G S board₀ k tail age p f g drift degree payload ordinary op₀ (S.firstWidth G.b p) (S.grainAt G.b p 0) cursor.ports.operandLanes cursor.ports.roleLanes
      cursor.ports.venue cursor.ports.io (cursor.ports.priorStart k cursor.floor) w (cursor.ports.afterPad k cursor.floor).archive)
local notation "u" => DatePorts.resetInputs G S board k tail age p f g drift degree payload ordinary op s₀ Z₀
  cursor.ports cursor.floor w space
local notation "ports" => cursor.ports
variable {description : BitDescription W} {R : ℕ} (number : Local description)
  (bounds : DatePorts.RangeRoom cursor.ports input description) (shape : WorldShape p R description)
  (label : NodeOrder.All description→Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op₀)

variable (geo : Geometry G S (⟨board₀,op₀,g,tail,p,f,drift,degree,payload,seats,ordinary,profile,header⟩ : Menu n h) k w age cursor)
    (widths : DatePorts.ArchiveWidths G S op₀ cursor.ports k tail p drift degree payload age)
local notation "realPanels" => RegisteredOperandPanels B p drift degree payload w ordinary cursor

include B space number bounds shape label geo widths in
abbrev MatchedRegisteredOperandPanels (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D)
    (ready : (u).Ready) (m : Memory w) (capAt : input.placement.cap=cap) : Prop := by
  subst n
  subst h
  subst f
  subst g
  subst tail
  have sameBoard : ctl.board=board₀:=eq_of_heq hb
  subst board₀
  subst op₀
  exact realPanels space number bounds shape label m degreeAt capAt ready geo.room.hosts geo.format.width
    geo.room.population.groups widths geo.arguments

variable (capacity : cursor.ports.venue.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)

variable (paid : B.Recorded p)
    {pointer : NodeOrder.All description→ℕ→Pointer}
    {flags : Fin (2^cursor.ports.venue.k)→Fin cursor.ports.nodes→Fin cursor.ports.operandHosts→Fin cursor.ports.venue.groups→ℕ}
include paid capacity in
theorem matched_operand_panels (hn : n₁=n) (hh : h₁=h) (hf : f₁=f) (hg : g₁=g) (ht : tail₁=tail)
    (hb : HEq ctl.board board₀) (ho : RotorSpec.ofRates ctl=op₀) (degreeAt : (old).degree=D) (ready : (u).Ready)
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
    MatchedRegisteredOperandPanels board₀ op₀ B p drift degree payload w ordinary seats profile header cursor space
      number bounds shape label geo widths hn hh hf hg ht hb ho degreeAt ready m capAt :=by
  subst n
  subst h
  subst f
  subst g
  subst tail
  have sameBoard : ctl.board=board₀:=eq_of_heq hb
  subst board₀
  subst op₀
  exact scheduled_operand_panels B p drift degree payload w ordinary seats profile header cursor capacity space
    number bounds shape label paid geo widths degreeAt ready m incoming gr fee capAt historyAt branch seen
    popFit popRead wireRoom oldPos oldWidth entryFits low score live degreePos headerBits hostBits ranksFit
    namesFit degFit laneRoom hubSpan pitchOld narrow word ceiling boardRoom elapsed sorted operandPos rolePos
    newFit sized actual

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
