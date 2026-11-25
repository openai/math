import OAI.Hierarchy.DescentOriginalFundedCourse
import OAI.Hierarchy.DescentDatedSeedAppendedProfile
import OAI.Hierarchy.DescentDatedSeedInitialHeld

import OAI.Hierarchy.DescentWideSeedOriginalInvoice

namespace OAI
/-! # The original funded calendar on the actual appended, checked and booted selector tape -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open scoped Classical Fin.CommRing
set_option cleanup.letToHave false
set_option maxRecDepth 12000
set_option quotPrecheck false
set_option hygiene false
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut) (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
local notation "board" => reset.board
local notation "op" => RotorSpec.ofRates reset
variable
    (drift degree degreeMax lo header : ℕ) (initial : RegisterTimeline.Position)
local notation "menu" => RegisterTimeline.fromProfiles G S board op k frozen p f g drift degree payload lo header (ch).layout
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces menu initial
local notation "model" i:arg a:arg tick:arg =>
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 1400000

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
variable {H extBits j r teams : ℕ} (startup:DescentDatedSeedStartup.Layout)
  (wide:Fintype.card (Vertex X)≤H) (Z extra:ℕ)
  (x₀:Fin extBits→Plane j r→Fin teams→Bool) (z₀:(ch).Pin⊕Hidden extBits j r teams→Bool)
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

attribute [local irreducible] completeImage DescentWideSeedFlags.countedAt Root.appended Root.widePackedImage SeedNamed.issued DatePorts.held

open Lean Elab Term in
local elab "fundedBallotInputs% " fn:term:arg "[" args:term,* "]" : term => do
  let f ← elabTerm fn none
  return mkAppN f (← args.getElems.mapM fun x => elabTerm x none)

open Lean Elab Term in
local elab "boardCourseArg% " fn:term:arg "[" args:term,* "]" : term => do
  let f ← elabTerm fn none
  let context ← getLCtx
  let xs ← args.getElems.mapM fun a => do
    if a.isIdent then
      if let some d := context.findFromUserName? a.getId then return d.toExpr
    elabTerm a none
  return mkAppN f xs

attribute [local irreducible] RunTrace.machine DateCode.history Path.snapshotRanks Path.dateReadbacks Path.Held

set_option maxHeartbeats 4000000 in
theorem original_funded_ballot (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0< sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (seedWord:2*digitsNeeded s≤payload)
    (sourceSpace:DescentPackedSeed.publicWords X+DescentDyadicSpan.span
      (DescentPackedSeed.Primitive.Source.jobs X (S).copies startup.seedWidth payload)≤ seedEnd)
    (live:0<lanes) (native:payload≤w) (signedWord:DescentSignedCableCodec.width 3 256*startup.packedLanes≤w)
    (fieldsFit:startup.operandBits*startup.operandLanes≤w)
    (placed:lo=DescentWideSeedFlags.selectorBase X (S).copies s payload (ch).layout.length)
    (above:front+extra≤header) (below:header<startup.base) (seedFits:limit<2^w)
    (seedPosition:initial=⟨entryPorts,limit⟩)
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (capture roof : ℕ) (startAfter:capture+(days).length≤ initial.floor)
    (roofAfter:(cursor (S).length).floor≤roof) (roofFits:roof<2^w) :
    let alive := ∃c,(ch).read votes=some c
    FundedDateInputs S proofCPU m header capture roof (fun i=>(cursor i).floor) col saved_
      ((trace (walk₀ votes)).path.dateReadbacks (DateCode.history proofCPU m) flags saved_ col
        ((ch).rows votes).length alive) ∧
    (alive→(trace (walk₀ votes)).path.Held header (DateCode.history proofCPU m (S).length)) ∧
    ∀c,(ch).read votes=some c→(trace c).path.snapshotRanks storedRanks (cursor (S).length).floor
      (DateCode.history proofCPU m (S).length) := by
  have booked : DescentWideSeedFlags.endInput X (S).copies s payload+
      (DescentPackedSeed.rows X (S).copies s payload+1)≤lo := by
    rw [placed]
    unfold DescentWideSeedFlags.selectorBase
    omega
  have stored := fundedBallotInputs% (@complete_appended_profile_after) [
    F, (ch).Pin, (inferInstance : Field F), S, G, op, k, cp, nP, H, w,
    extBits, j, r, teams, X, (S).initialDigits ordinary.radix, wide, startup, header, payload, Z,
    s, (ch).seed, lo, G.C, storage, (ch).layout, origin, extra, x₀, z₀, appendix,
    seedWord, sourceSpace, live, native, signedWord, fieldsFit, booked,
    (show origin ≤ origin from le_rfl), above, below, seedFits]
  let b := trace (walk₀ votes)
  have seedHeld := initial_held_of_public G op X ((S).initialDigits ordinary.radix) wide startup
    header payload Z b.origin checked signedWord fieldsFit below sourceSpace live native seedFits
  have initialized := complete_after_count G op X ((S).initialDigits ordinary.radix) wide startup
    header payload Z b.origin (b.origin.seed.hostSize.le.trans wide) checked signedWord fieldsFit below
    sourceSpace live native seedFits
  have oldHeader : header < initial.floor := by
    rw [seedPosition]
    exact stored.2.1
  have held : initial.ports.held (trace (walk₀ votes)).origin.source initial.floor m := by
    rw [seedPosition]
    exact seedHeld
  let purchased := boardCourseArg% (@original_funded_course) [
    F, (inferInstance : Field F), cp, nP, X, G, n, h, C, f, g, p, cut,
    t, rate, τ, β, siteCount, payload, ordinary, reset, branch, positive, room, shorten,
    w, fit, drift, degree, degreeMax, lo, header, initial, driftR, ratio,
    K, headRate, grant, purchase, returns, receiver, growth, sites, input, coeff, original, pre,
    positiveK, headerFits, machine, matcher, signed, palette, bin, sockets, nonempty, split,
    stored.1, oldHeader, votes, m, stored.2.2, observed, seedDegree, degreeRoom, resetWords, capture, roof, startAfter, roofAfter, roofFits, held, initialized.2.1]
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof := (← Lean.Meta.getLocalDeclFromUserName `purchased).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []


end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
