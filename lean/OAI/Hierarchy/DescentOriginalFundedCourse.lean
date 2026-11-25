import OAI.Hierarchy.DescentProfiledMeter
import OAI.Hierarchy.DescentProfiledOriginalCourse
import OAI.Hierarchy.DescentProfiledFundedDates
import OAI.Hierarchy.DescentNamedEarnedSnapshotRanks

namespace OAI
/-! # The registered original course, private charge and snapshot ranks on the same ballot -/
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

open Lean Elab Term in
local elab "fundedRankArgs% " f:term:arg "[" xs:term,* "]" : term => do
  let fn ← elabTerm f none
  return mkAppN fn (← xs.getElems.mapM fun x => elabTerm x none)

private theorem selectedCourseFacts {Choice : Type*} {answer : Option Choice} (actual : Choice)
    (dates : Prop → Prop) (held : Prop) (ranks : Choice → Prop)
    (chosen : ∀c, answer=some c → c=actual)
    (funded : dates (answer=some actual) ∧ (answer=some actual → held))
    (published : answer=some actual → ranks actual) :
    dates (∃c,answer=some c) ∧ ((∃c,answer=some c) → held) ∧ ∀c,answer=some c → ranks c := by
  have accepted : (∃c,answer=some c) = (answer=some actual) := by
    apply propext
    constructor
    · rintro ⟨c,h⟩
      exact (chosen c h) ▸ h
    · exact fun h => ⟨actual,h⟩
  rw [accepted]
  refine ⟨funded.1,funded.2,?_⟩
  intro c selected
  obtain rfl := chosen c selected
  exact published selected

attribute [local irreducible] RunTrace.machine DateCode.history Path.snapshotRanks Path.dateReadbacks Path.Held

private theorem original_funded_course_assembly (K headRate : ℕ)
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
    (beforeHeader:lo+extent storage (ch).layout≤ header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Word w))
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (capture roof : ℕ) (startAfter:capture+(days).length≤ initial.floor)
    (roofAfter:(cursor (S).length).floor≤roof) (roofFits:roof<2^w)
    (bootstrap:initial.ports.held (traces (walk₀ votes)).first initial.floor m)
    (zero:m header=0)
    (course : RegisterTimeline.OriginalCourse traces menu initial (walk₀ votes) m ((ch).rows votes).length
      ((ch).read votes=some (walk₀ votes)))
    (meter : ∀i (e:(traces (walk₀ votes)).path.Event i),(ch).read votes=some (walk₀ votes) →
      Path.Event.incoming (t:=traces (walk₀ votes)) e (cursor i) (DateCode.history cpu m i) →
      privateStep traces menu initial (walk₀ votes) m header i e) :
    let alive := ∃c,(ch).read votes=some c
    FundedDateInputs S proofCPU m header capture roof (fun i=>(cursor i).floor) col saved_
      ((traces (walk₀ votes)).path.dateReadbacks (DateCode.history proofCPU m) flags saved_ col
        ((ch).rows votes).length alive) ∧
    (alive→(traces (walk₀ votes)).path.Held header (DateCode.history proofCPU m (S).length)) ∧
    ∀c,(ch).read votes=some c→(trace c).path.snapshotRanks storedRanks (cursor (S).length).floor
      (DateCode.history proofCPU m (S).length) := by
  let c₀:=(walk₀ votes)
  have cellCost (i:ℕ) (e:RunTrace.Events traces i) (cells:geom i) :=
    ((profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth
      sites input coeff original pre positiveK headerFits machine i e).2 cells).1
  have runCell :=
    profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth
      sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split
      beforeHeader oldHeader
  have bus : payload≤w :=
    (Nat.le_mul_of_pos_left _ (show 0<t+1+max K headRate+2 by omega)).trans machine
  have allRows:=profiled_funded_course X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus positiveK seedDegree degreeRoom pre cellCost runCell
    capture roof beforeHeader oldHeader startAfter roofAfter roofFits votes m oldVotes c₀ ((ch).rows votes).length
    ((ch).read votes=some c₀) observed bootstrap course meter zero
  have chosen (c:(last).Choice) (selected:(ch).read votes=some c) : c=c₀ := by
    have written:=((ch).read_iff _ _).mp selected
    change c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes
    have stored : (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow ((ch).store c) = c :=
      (normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c
    exact stored.symm.trans (congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow written.symm)
  apply selectedCourseFacts c₀ (fun live => FundedDateInputs S proofCPU m header capture roof
    (fun i=>(cursor i).floor) col saved_ ((traces c₀).path.dateReadbacks
      (DateCode.history proofCPU m) flags saved_ col ((ch).rows votes).length live))
    ((traces c₀).path.Held header (DateCode.history proofCPU m (S).length))
    (fun c => (trace c).path.snapshotRanks storedRanks (cursor (S).length).floor
      (DateCode.history proofCPU m (S).length)) chosen allRows
  intro selected
  exact fundedRankArgs% (@profiled_course_snapshot_ranks) [
    F, (inferInstance : Field F), cp, nP, X, G, S, k, cut, frozen, n, h, C, f, g, p,
    ordinary, reset, branch, positive, room, shorten, w, fit, drift, degree, payload,
    lo, header, initial, bus, positiveK, seedDegree, degreeRoom, pre, cellCost, runCell,
    votes, c₀, m, selected, bootstrap, course, oldHeader, resetWords]


private theorem funded_from_course_and_proper_meter (K headRate : ℕ)
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
    (beforeHeader:lo+extent storage (ch).layout≤ header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Word w))
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (capture roof : ℕ) (startAfter:capture+(days).length≤ initial.floor)
    (roofAfter:(cursor (S).length).floor≤roof) (roofFits:roof<2^w)
    (bootstrap:initial.ports.held (traces (walk₀ votes)).first initial.floor m)
    (zero:m header=0)
    (course : RegisterTimeline.OriginalCourse traces menu initial (walk₀ votes) m ((ch).rows votes).length
      ((ch).read votes=some (walk₀ votes)))
 :
    let alive := ∃c,(ch).read votes=some c
    FundedDateInputs S proofCPU m header capture roof (fun i=>(cursor i).floor) col saved_
      ((traces (walk₀ votes)).path.dateReadbacks (DateCode.history proofCPU m) flags saved_ col
        ((ch).rows votes).length alive) ∧
    (alive→(traces (walk₀ votes)).path.Held header (DateCode.history proofCPU m (S).length)) ∧
    ∀c,(ch).read votes=some c→(trace c).path.snapshotRanks storedRanks (cursor (S).length).floor
      (DateCode.history proofCPU m (S).length) := by
  let c₀:=(walk₀ votes)
  have cellCost (i:ℕ) (e:RunTrace.Events traces i) (cells:geom i) :=
    ((profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth
      sites input coeff original pre positiveK headerFits machine i e).2 cells).1
  have runCell :=
    profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth
      sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split
      beforeHeader oldHeader
  have bus : payload≤w :=
    (Nat.le_mul_of_pos_left _ (show 0<t+1+max K headRate+2 by omega)).trans machine
  have meter := profiled_meter X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial bus positiveK seedDegree degreeRoom pre cellCost runCell
    beforeHeader oldHeader votes m oldVotes observed
  exact original_funded_course_assembly X G t rate τ β siteCount payload ordinary reset branch positive
    room shorten w fit drift degree degreeMax lo header initial K headRate grant purchase returns receiver
    growth sites input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty
    split beforeHeader oldHeader votes m oldVotes observed seedDegree degreeRoom resetWords capture roof startAfter
    roofAfter roofFits bootstrap zero course meter


open Lean Elab Term in
local elab "boardCourseArg% " fn:term:arg "[" args:term,* "]" : term => do
  let f ← elabTerm fn none
  let context ← getLCtx
  let xs ← args.getElems.mapM fun a => do
    if a.isIdent then
      if let some d := context.findFromUserName? a.getId then return d.toExpr
    elabTerm a none
  return mkAppN f xs

theorem original_funded_course (K headRate : ℕ)
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
    (beforeHeader:lo+extent storage (ch).layout≤ header) (oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Word w))
    (observed:ObservationRoom G S payload w)
    (seedDegree:initial.ports.venue.degree=3) (degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (resetWords:SnapshotWordRoom S n h k frozen p f g payload w)
    (capture roof : ℕ) (startAfter:capture+(days).length≤ initial.floor)
    (roofAfter:(cursor (S).length).floor≤roof) (roofFits:roof<2^w)
    (bootstrap:initial.ports.held (trace (walk₀ votes)).origin.source initial.floor m)
    (zero:m header=0) :
    let alive := ∃c,(ch).read votes=some c
    FundedDateInputs S proofCPU m header capture roof (fun i=>(cursor i).floor) col saved_
      ((trace (walk₀ votes)).path.dateReadbacks (DateCode.history proofCPU m) flags saved_ col
        ((ch).rows votes).length alive) ∧
    (alive→(trace (walk₀ votes)).path.Held header (DateCode.history proofCPU m (S).length)) ∧
    ∀c,(ch).read votes=some c→(trace c).path.snapshotRanks storedRanks (cursor (S).length).floor
      (DateCode.history proofCPU m (S).length) := by
  let course := boardCourseArg% (@profiled_original_course) [
    F, (inferInstance : Field F), cp, nP, X, G, n, h, C, f, g, p, cut,
    t, rate, τ, β, siteCount, payload, ordinary, reset, branch, positive, room, shorten,
    w, fit, drift, degree, degreeMax, lo, header, initial, driftR, ratio,
    K, headRate, grant, purchase, returns, receiver, growth, sites, input, coeff, original, pre,
    positiveK, headerFits, machine, matcher, signed, palette, bin, sockets, nonempty, split,
    beforeHeader, oldHeader, votes, m, oldVotes, observed, seedDegree, degreeRoom, resetWords]
  let purchased := boardCourseArg% (@funded_from_course_and_proper_meter) [
    F, (inferInstance : Field F), cp, nP, X, G, n, h, C, f, g, p, cut,
    t, rate, τ, β, siteCount, payload, ordinary, reset, branch, positive, room, shorten,
    w, fit, drift, degree, degreeMax, lo, header, initial, driftR, ratio,
    K, headRate, grant, purchase, returns, receiver, growth, sites, input, coeff, original, pre,
    positiveK, headerFits, machine, matcher, signed, palette, bin, sockets, nonempty, split,
    beforeHeader, oldHeader, votes, m, oldVotes, observed, seedDegree, degreeRoom, resetWords, capture, roof, startAfter, roofAfter, roofFits, bootstrap, zero, course]
  run_tac Lean.Elab.Tactic.withMainContext do
    let proof := (← Lean.Meta.getLocalDeclFromUserName `purchased).toExpr
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
