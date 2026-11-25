import OAI.Hierarchy.DescentNamedProfiledOrdinaryAdvance
import OAI.Hierarchy.DescentRegisterOriginalCourse
import OAI.Hierarchy.DescentProfiledResetAdvance
import OAI.Hierarchy.DescentProfiledResetWords

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler

private theorem Path.Event.originalCourseCases {F P : Type} [Field F] [Fintype P]
    {d k wire hist len : ℕ} {bits : P → ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {q ε : ℝ} (tr : RunTrace G q ε S k wire hist len bits d)
    (age : ℕ) (motive : tr.path.Event age → Prop)
    (ordinary : ∀ {U : MarkedWorld F d P bits} {z D z' D' : ℕ} {u : ℝ}
      {src : Reached U G q ε S k age z D wire hist} {he : 0 ≤ ε}
      {T : StageInput U G u ε} {choice : (T.result he).Choice}
      {norm : Normalize ((T.result he).state choice)}
      {dst : Reached norm.result G q ε S k (age+1) z' D' wire hist}
      (before : Path tr.first src) (ticket : OrdinaryLink src he T choice norm dst)
      (after : Path dst tr.last) (cut : (before.ordinary ticket).append after = tr.path),
      motive (.ordinary before ticket after cut))
    (reset : ∀ {U : MarkedWorld F d P bits} {z D n h C f g cut tail : ℕ}
      {src : Reached U G q ε S k age z D wire hist}
      {ctl : ResetRates G S k D n h C f g cut tail} (before : Path tr.first src)
      (closed : ClosedReset src ctl) (after : Path closed.next tr.last)
      (placed : (before.reset closed).append after = tr.path),
      motive (.reset before closed after placed))
    (event : tr.path.Event age) : motive event := by
  cases event with
  | ordinary before ticket after cut => exact ordinary before ticket after cut
  | reset before closed after placed => exact reset before closed after placed

end Hierarchy.DescentSixParty.Chronology

/-! # The active original history on the fixed compiler's public calendar -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical Fin.CommRing
noncomputable section
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] RegisterTimeline.advances DateCode.Runs Path.Event.incoming Path.Event.outgoing
attribute [local irreducible] Origin.source Origin.archivePackage SeedNamed.issued
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g)) cut)
    (reset : ResetRates G (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))) (groupBits t (Nat.log 2 payload/(2*β)) (hostRate t rate) (capRate G t g) (cutRate t f g))
      (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β))))
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p)
    (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
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
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a:RegisterTimeline.Position).floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 6000000

local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "offer" => ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload
local notation "slot" => ProfiledPosition G board op t f g rate τ drift degreeMax β payload

local notation "guardAt" => profiledGuard X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree lo header initial
local notation:max "geom" i:arg => Geometry G S menu k w i (cursor i)
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
local notation:max "walk₀" votes:arg => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

set_option maxHeartbeats 6000000
open Lean Elab Tactic Meta in
elab "closeProfiledCourseStep " func:ident " [" args:term,* "]" : tactic => withMainContext do
  let name ← resolveGlobalConstNoOverload func
  let h ← mkConstWithFreshMVarLevels name
  let ctx ← getLCtx
  let terms ← args.getElems.mapM fun a => do
    if a.isIdent then
      if let some decl := ctx.findFromUserName? a.getId then
        return decl.toExpr
    elabTerm a none
  (← getMainGoal).assign (mkAppN h terms)
  replaceMainGoal []

private abbrev ProfiledCourseClaim : Prop := ∀ (K headRate : ℕ)
    (_grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (_purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (_returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (_receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (_growth : drift+1 ≤ scale J₀ driftR) (_sites : siteCount≤(2^payload)^2)
    (_input : p≤ payload) (_coeff : degree≤ degreeMax) (_original : (S).firstWidth G.b p≤ payload)
    (_pre : Geometry G S menu k w 0 initial) (_positiveK : 0< k)
    (_headerFits : initial.floor≤2^(headRate*payload)) (_machine : (t+1+max K headRate+2)*payload≤ w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤ payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0< sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤ header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    (_oldVotes:∀a∈shelves storage lo 0 (ch).layout,∀j:Fin (slots a.src.seats storage),
      m (a.base+j.val)=((packed a.src.pin votes storage j.val).val:Word w))
    (_observed:ObservationRoom G S payload w)
    (_seedDegree:initial.ports.venue.degree=3) (_degreeRoom:maximumDegree ((S).rounds+1)+1<2^w)
    (_resetWords:SnapshotWordRoom S n h k frozen p f g payload w),
    RegisterTimeline.OriginalCourse traces menu initial (walk₀ votes) m ((ch).rows votes).length
      ((ch).read votes=some (walk₀ votes))
theorem profiled_original_course :
    ProfiledCourseClaim (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload ordinary reset
      branch positive room shorten w fit drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits
    machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m oldVotes
    observed seedDegree degreeRoom resetWords
  have placed (j:ℕ) (cutEvt:RunTrace.Events traces j) :=
      (profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
        w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
        input coeff original pre positiveK headerFits machine j cutEvt).1
  have bus:payload≤ w := (Nat.le_mul_of_pos_left _ (show 0< t+1+max K headRate+2 by omega)).trans machine
  refine ⟨?_,profiled_reset_words X G S ordinary reset branch positive room shorten w fit drift degree payload
    lo header initial bus seedDegree degreeRoom pre placed resetWords votes (walk₀ votes) m⟩
  intro i ev
  refine Path.Event.originalCourseCases (traces (walk₀ votes)) i
    (fun event => RegisterTimeline.advances traces menu initial (walk₀ votes) m
      ((ch).rows votes).length ((ch).read votes=some (walk₀ votes)) i event) ?_ ?_ ev
  · intro W z D z' D' q prior nonneg T choice norm next before ticket after joined
    let e:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after joined⟩
    have atCut : geom i :=(profiled_installed X G S ordinary reset branch positive room shorten w fit board op frozen
      drift degree payload lo header initial pre placed i e).1
    closeProfiledCourseStep profiled_ordinary_advance [F, (inferInstance : Field F), cp, nP, X, G,
      n, h, C, f, g, p, cut, (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload / (2*β))),
      t, rate, τ, β, siteCount, payload, ordinary, reset, branch, positive, room, shorten,
      w, fit, n, h, (reset.board), (RotorSpec.ofRates reset), drift, degree, degreeMax,
      lo, header, initial, driftR, ratio, K, headRate, grant, purchase, returns, receiver,
      growth, sites, input, coeff, original, pre, positiveK, headerFits, machine, matcher, signed,
      palette, bin, sockets, nonempty, split, beforeHeader, oldHeader, votes, m, oldVotes,
      W, i, z, D, z', D', q, nonneg, prior, T, choice, norm, next, ticket, before, after, joined, atCut, observed]
  · intro W z D rn rh rC rf rg rCut rTail prior ctl before B after joined
    exact profiled_reset_advance X G S ordinary reset branch positive room shorten w fit drift degree payload
      lo header initial bus seedDegree degreeRoom (walk₀ votes) m before B after joined pre placed resetWords
      ((ch).rows votes).length ((ch).read votes=some (walk₀ votes))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
