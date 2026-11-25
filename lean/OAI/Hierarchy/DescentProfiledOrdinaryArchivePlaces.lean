import OAI.Hierarchy.DescentNamedProfiledCalendarRate
import OAI.Hierarchy.DescentNamedAllRegisterMoves
import OAI.Hierarchy.DescentRegisteredHeaderPlaces

namespace OAI
/-! # The original data coordinates of the next ordinary archive on the selected calendar -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentCompiler
noncomputable section

private theorem ordinaryArchiveNextPorts {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F}
    {S : AtomSchedule} {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {bn bd : ℕ} (b : Menu bn bd) (initial : Position)
    (c : C) {i z D z' D' : ℕ} {rate : ℝ} {U : MarkedWorld F d P bits}
    {src : Reached U G q ε S k i z D wire hist} {he : 0 ≤ ε}
    {T : StageInput U G rate ε} {choice : (T.result he).Choice}
    {norm : Normalize ((T.result he).state choice)}
    {dst : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice norm dst)
    (after : Path dst (traces c).last) (joined : (before.ordinary ticket).append after = (traces c).path)
    (cells : Geometry G S b k w i (calendar (w:=w) traces b initial i))
    (placed : fitsAt traces b initial (w:=w) i ⟨c, .ordinary before ticket after joined⟩)
    (common : ∀ l r : RunTrace.Events traces i, ∀ x y : Move w,
      issued traces b i l (calendar (w:=w) traces b initial i) x →
      issued traces b i r (calendar (w:=w) traces b initial i) y → x = y) :
    let pos := calendar (w:=w) traces b initial i
    (calendar (w:=w) traces b initial (i+1)).ports =
      DatePorts.ordinaryPorts pos.ports ticket b.op b.gain b.tail b.p b.f b.drift
        b.degreeLimit b.payload (b.seats i) pos.floor b.ordinary := by
  let e : RunTrace.Events traces i := ⟨c, .ordinary before ticket after joined⟩
  obtain ⟨move,hit,_,_⟩ := placed cells
  have held := returned traces b initial i e move hit (fun d y hy => common d e y move hy hit)
  obtain ⟨_,_,rfl⟩ := hit
  exact congrArg Position.ports held.2

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 12000
set_option cleanup.letToHave false
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
local notation "s" => (S).firstWidth G.b p
local notation "trace" => issued X G S ordinary reset branch positive room shorten
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
set_option maxHeartbeats 6000000

local notation "geom" i:arg => Geometry G S menu k w i (cursor i)
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

local notation "cert_" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last_" => Epochs.finish G _ _ (cert_).choose

private def archiveWalk (votes : (ch).Pin → Bool) : (last_).Choice :=
  (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

attribute [local irreducible] archiveWalk SeedNamed.issued normalizedPackedChart Origin.source Origin.archivePackage

local notation "walk₀" votes:arg =>
  archiveWalk X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit votes


local notation "org" vote:arg => (trace (walk₀ vote)).origin

open Lean Meta Elab Term in
local elab "registeredArchive% " fn:term:arg br:term:arg tk:term:arg "[" xs:term,* "]" : term => do
  let f ← elabTerm fn none
  let b ← elabTerm br none
  let t ← elabTerm tk none
  let some bt ← whnfUntil (← inferType b) ``SeedNamed.Branch | throwError "expected a named branch"
  let some tt ← whnfUntil (← inferType t) ``OrdinaryLink | throwError "expected an ordinary link"
  unless bt.getAppFn.isConstOf ``SeedNamed.Branch && tt.getAppFn.isConstOf ``OrdinaryLink do
    throwError "expected branch/link, got {bt.getAppFn} ({bt.getAppNumArgs}) and {tt.getAppFn} ({tt.getAppNumArgs})"
  let bs := bt.getAppArgs
  let ts := tt.getAppArgs
  unless bs.size == 20 && ts.size == 25 do throwError "unexpected branch or ordinary-link telescope"
  let branchArgs := bs.extract 0 14 ++ #[bs[17]!, bs[14]!, bs[15]!, bs[16]!, bs[18]!, bs[19]!, b]
  let event := #[ts[11]!, ts[12]!, ts[13]!, ts[14]!, ts[22]!, ts[23]!, ts[8]!, ts[17]!,
    ts[19]!, ts[18]!, ts[20]!, ts[21]!, ts[24]!, t]
  return mkAppN f (branchArgs ++ event ++ (← xs.getElems.mapM fun x => elabTerm x none))

theorem profiled_ordinary_archive_places (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤ payload) (coeff : degree≤ degreeMax) (original : (S).firstWidth G.b p≤ payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0< k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤ w)
    (votes : (ch).Pin→Bool)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {n:Normalize ((T.result nonneg).state choice)}
    {next:Reached n.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice n next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (cells : geom i) (whole : (before.ordinary ticket).whole p) :
    DatePorts.RangeRoom (cursor (i+1)).ports next ((before.ordinary ticket).archive p positive
      (org votes).archive whole).bit :=by
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  have paid:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i (cursor i)
  have position := RegisterTimeline.ordinaryArchiveNextPorts traces menu initial (walk₀ votes)
    before ticket after located cells paid.1 common
  have lanes := (paid.2 cells).1.1
  have physical := registeredArchive% (@Branch.header_archive_places) (trace (walk₀ votes)) ticket [
    before, after, located, op, frozen, drift, degree, payload, ((menu).seats i), (cursor i).floor,
    (cursor i).ports, (menu).ordinary, positive, reset.height, whole, lanes]
  exact (congrArg (fun ports : DatePorts => DatePorts.RangeRoom ports next
    ((before.ordinary ticket).archive p positive (org votes).archive whole).bit) position).mpr physical

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
