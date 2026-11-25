import OAI.Hierarchy.DescentOriginalFundedBallot
import OAI.Hierarchy.DescentProfiledMountedDateRows
import OAI.Hierarchy.DescentOriginalRoleMount

namespace OAI
/-! # The terminal raster rows on the original appended and checked ballot -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g cut W piece q : ℕ}
local notation "p" => W*piece
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option hygiene false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound ((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).capGain) (positive : 0 < (W*piece)) (room : 10*(X.size+1) ≤ ((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).firstWidth G.b (W*piece)) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
local notation "drift" => max 1 (max reset.bitsR (C*reset.bitsR))
variable
    (degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 6000000

local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "offer" => ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload
local notation "slot" => ProfiledPosition G board op t f g rate τ drift degreeMax β payload

local notation "guardAt" => profiledGuard X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree lo header initial
local notation "geom" i:arg => Geometry G S menu k w i (cursor i)
local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

local notation "execute" => profiledExecution X G S ordinary reset branch positive room shorten w fit
  board op frozen drift degree payload lo header initial
open DescentPackedEpochShelves
local notation "storage" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "family" => fun i H=>SignedStage.atDate G S g k i H

open DescentPackedProfileTape DescentPackedProfileInstall
local notation "cpu" => RegisterTimeline.instruction (w:=w) traces menu initial
local notation "walk₀" votes:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

local notation "proofCPU" => RunTrace.machine traces (fun i _=>cpu i)
local notation "days" => countDates 0 (kindCalendar (S).rounds (S).height)
local notation "flags" => RegisterTimeline.Menu.resetFlag S
local notation "col" => fun i=>(menu).selectorAt G S k i (cursor i)
local notation "saved_" => fun i=>(menu).rotationAt G S k i (cursor i)
local notation "storedRanks" => SnapshotCalendar reset (kindCalendar (S).rounds (S).height)
  (capCalendar G.b (S).rounds g (S).height) (RegisterTimeline.snapshotDirectory (w:=w) traces menu initial)

open DescentDatedSeedStartup DescentDatedSeedStartup.Input DescentExterior DescentExteriorShelf
local notation "extBits" => Fintype.card (Port nP X.width)
local notation "teams" => s
variable {H j r : ℕ} (startup:DescentDatedSeedStartup.Layout)
  (wide:Fintype.card (Vertex X)≤ H) (Z extra:ℕ)
  (x₀:Fin (Fintype.card (Port nP X.width))→Plane j r→Fin ((((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).firstWidth G.b (W*piece)))→Bool) (z₀:((normalizedPackedChart X G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port nP X.width)) j r ((((stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))).firstWidth G.b (W*piece)))→Bool)
  (appendix:Memory w)
local notation "votes" => (z₀∘Sum.inl)
local notation "origin" => end_ (lo+extent storage (ch).layout) G.C storage
local notation "front" => origin+17*DescentExteriorShelf.span j r teams extBits
local notation "raw" => Root.appended front extra
  (Root.widePackedImage X (S).copies s payload w (ch).seed lo G.C storage (ch).layout origin x₀ z₀) appendix
local notation "checked" => DescentWideSeedFlags.countedAt X (S).copies s payload (ch).seed votes raw
local notation "m" => completeImage G op X ((S).initialDigits ordinary.radix) wide startup header payload Z checked
local notation "top" => endAddress X startup H ((S).groupCount 0) k
local notation "seedEnd" => (nodeChart startup k H ((S).groupCount 0)).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op startup.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X (S).copies startup.seedWidth payload
  k H ((S).groupCount 0) lanes seedEnd
local notation "entryPorts" => DatePorts.initial G op X (S).copies startup k H ((S).groupCount 0) payload Z

open DescentExteriorReplay DescentTerminalFixedSlices DescentTerminalRoleTables DescentPrimitivePalette
open DescentTerminalGraphPositions DescentActorRaster DescentPackedColony DescentTerminalEmitter
open DescentTerminalCombinedRole DescentTerminalSiteShelves DescentTerminalScalarTransposes
variable (headerRows paidRows replayBase matrixTable roleBase capture : ℕ)
local notation "dateRotation" => saved_
local notation "snapshots" => storedRanks
local notation "dateAge" => (S).length-1
local notation "old" => cursor dateAge
local notation "ordinaryAt" => (menu).ordinary
local notation "previousDate" => (old).ports.venue
local notation "operandLanes" => (old).ports.operandLanes
local notation "primitiveLanes" => (old).ports.roleLanes
local notation "priorAddress" => (old).ports.io.wire
local notation "rosterBank" => (old).ports.io.roster
local notation "datedFloor" => (old).ports.priorStart k (old).floor
local notation "Z₀" => (S).grainAt G.b p 0
local notation "dateMachine" => PhysicalReset.scheduled G S board k frozen dateAge p f g drift degree payload
  ordinaryAt op s Z₀ operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "datePhase" => Phase.scheduled G S board k frozen dateAge p f g drift degree payload ordinaryAt op
  operandLanes primitiveLanes previousDate priorAddress rosterBank datedFloor
local notation "dateOut" => (datePhase).output
local notation "dateSpec" => Branch.preflightSpec X G S k g p frozen (Branch.geometryFormat G S k g p frozen q drift op headerRows paidRows)
local notation "earlyFloor" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k frozen replayBase j r s extBits
local notation "sliceEnd" => (datePhase).stop earlyFloor
local notation "lookupBase" => (Branch.replayCalendar X S k frozen j r snapshots).packetEnd sliceEnd
local notation "censusBase" => ((dateSpec).scanPages lookupBase q).stop
local notation "dateColors" => DescentPrimitivePalette.colors G s Z₀ op
local notation "roleBankBits" => fun roleField:Fin 6=>DescentTerminalCombinedRole.width dateColors (max 8 (2^(S).capGain))
  (NativeBranch.privateSlotCapacity G S drift) p drift roleField*((S).epochPower^(S).localTokenExponent)*(dateSpec).groups
local notation "captureSource" => fun i:ℕ=>col ((days)[i]?.getD 0)
local notation "lastMem" => DateCode.history proofCPU m (S).length
local notation "captured" => DescentLowCountBook.output capture captureSource lastMem (days).length

attribute [local irreducible] completeImage DescentWideSeedFlags.countedAt Root.appended Root.widePackedImage SeedNamed.issued DatePorts.held

open Lean Elab Term in
local elab "originalMountedInputs% " fn:term:arg "[" args:term,* "]" : term => do
  let f ← elabTerm fn none
  return mkAppN f (← args.getElems.mapM fun x => elabTerm x none)

attribute [local irreducible] RunTrace.machine DateCode.history Path.snapshotRanks Path.dateReadbacks Path.Held

theorem original_funded_mounted_registered (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ TerminalScale.scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0< sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (seedWord:2*digitsNeeded s≤ payload)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span
      (DescentPackedSeed.Primitive.Source.jobs X (S).copies startup.seedWidth payload)≤ seedEnd)
    (live:0< lanes) (native:payload≤ w) (signedWord:DescentSignedCableCodec.width 3 256*startup.packedLanes≤ w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤ w)
    (placed:lo=DescentWideSeedFlags.selectorBase X (S).copies s payload (ch).layout.length)
    (above:front+extra≤ header) (below:header< startup.base) (seedFits:limit<2^w)
    (seedPosition:initial=⟨entryPorts,limit⟩)
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (c₀:(last).Choice) (selected:(ch).read votes=some c₀)
    (startAfter:capture+(days).length≤ initial.floor)
    (roofAfter:(cursor (S).length).floor≤ replayBase)
    (maskRoom:(dateSpec).maskBase censusBase<2^w) (shops:0<(dateSpec).scalar.shops)
    (matrix:matrixTable+32*DescentExteriorShelf.span j r s extBits≤ replayBase)
    (signedPitch:(dateOut).venue.next.signedLanes=(S).groupCount (S).length)
    (ranks:∀i<(S).length,∀bank,(snapshots).compact i=some bank→bank.Fits w replayBase)
    (roleRoom:roleBase+DescentTerminalRoleTables.count roleBankBits≤ replayBase)
    (mount:RoleMount w roleBase replayBase) (beforeRom:(cursor (S).length).floor≤ roleBase) :
    ∃din:(dateMachine).DateInputs ((dateMachine).stageStart datedFloor) w,
      WideRegisteredDateRows (q:=q) (j:=j) (rest:=r) (W:=W) (piece:=piece)
        (X:=X) (G:=G) («S»:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
        (positive:=positive) (room:=room) (shorten:=shorten) (c:=c₀) («board»:=board)
        («dateAge»:=dateAge) (dateDegree:=degree) (datePayload:=payload) («ordinaryAt»:=ordinaryAt)
        («operandLanes»:=operandLanes) («primitiveLanes»:=primitiveLanes) («previousDate»:=previousDate)
        («priorAddress»:=priorAddress) («rosterBank»:=rosterBank) («datedFloor»:=datedFloor)
        (replayBase:=replayBase) (matrixTable:=matrixTable) («dateRotation»:=dateRotation)
        («snapshots»:=snapshots) (roleBase:=roleBase) (dateInput:=din)
        (headerRows:=headerRows) (paidRows:=paidRows) (datedMem:=mount.phase.image captured) :=by
  have route:=((ch).read_iff _ _).mp selected
  have actual:c₀=walk₀ votes:=by
    exact ((congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow route).trans ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c₀)).symm
  subst c₀
  have booked : DescentWideSeedFlags.endInput X (S).copies s payload+
      (DescentPackedSeed.rows X (S).copies s payload+1)≤lo := by
    rw [placed]
    unfold DescentWideSeedFlags.selectorBase
    omega
  have stored := originalMountedInputs% (@complete_appended_profile_after) [
    F, (ch).Pin, (inferInstance : Field F), S, G, op, k, cp, nP, H, w,
    extBits, j, r, teams, X, (S).initialDigits ordinary.radix, wide, startup, header, payload, Z,
    s, (ch).seed, lo, G.C, storage, (ch).layout, origin, extra, x₀, z₀, appendix,
    seedWord, sourceSpace, live, native, signedWord, fieldsFit, booked,
    (show origin ≤ origin from le_rfl), above, below, seedFits]
  let b := trace (walk₀ votes)
  have seedHeld := initial_held_of_public G op X ((S).initialDigits ordinary.radix) wide startup
    header payload Z b.origin checked signedWord fieldsFit below sourceSpace live native seedFits
  have oldHeader : header < initial.floor := by
    rw [seedPosition]
    exact stored.2.1
  have held : initial.ports.held (traces (walk₀ votes)).first initial.floor m := by
    dsimp only [traceAt]
    rw [seedPosition]
    exact seedHeld
  let course := originalMountedInputs% (@profiled_original_course) [
    F, (inferInstance : Field F), cp, nP, X, G, n, h, C, f, g, p, cut,
    t, rate, τ, β, siteCount, payload, ordinary, reset, branch, positive, room, shorten,
    w, fit, drift, degree, degreeMax, lo, header, initial, driftR, ratio,
    K, headRate, grant, purchase, returns, receiver, growth, sites, input, coeff, original, pre,
    positiveK, headerFits, machine, matcher, signed, palette, bin, sockets, nonempty, split,
    stored.1, oldHeader, votes, m, stored.2.2, observed, seedDegree, degreeRoom, resetWords]
  have placedAt (i:ℕ) (e:RunTrace.Events traces i) :=
    (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
      input coeff original pre positiveK headerFits machine i e).1
  have reel := profiled_reel_range X G S ordinary reset branch positive room shorten w menu initial
    rfl rfl rfl pre placedAt (walk₀ votes)
  have spinning (i : ℕ) (hi : i<(S).length) : dateRotation i<replayBase :=
    ((reel i hi (dateRotation i) (Or.inr rfl)).2 (S).length hi).trans_le roofAfter
  have liveCut : (trace (walk₀ votes)).path.selections.length < ((ch).rows votes).length ∨
      (ch).read votes=some (walk₀ votes) := Or.inr selected
  have previous : initial.ports.held (trace (walk₀ votes)).origin.source initial.floor m := by
    simpa only [traceAt] using held
  have fitsWord : 0<w := (positive.trans_le input).trans_le native
  exact originalMountedInputs% (@profiled_mounted_date_rows) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, frozen, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, (walk₀ votes), j, r, w, observed.height,
    degree, payload, lo, header, initial, m, headerRows, paidRows, replayBase, matrixTable,
    roleBase, dateRotation, snapshots, fit, native, seedDegree, degreeRoom, pre, placedAt,
    resetWords, ((ch).rows votes).length, ((ch).read votes=some (walk₀ votes)), previous,
    course, liveCut, maskRoom, fitsWord, shops, spinning, matrix, signedPitch, ranks, roleRoom,
    roofAfter, capture, (days).length, captureSource, startAfter, mount, beforeRom]

end
end Hierarchy.DescentSixParty.SeedNamed

-- Skip the costly local suggestion index for these large theorem types during export.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
  ["original_funded_mounted_registered"] ++ prior

end OAI
