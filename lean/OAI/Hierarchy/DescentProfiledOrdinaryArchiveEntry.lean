import OAI.Hierarchy.DescentNamedProfiledCalibratedExecution
import OAI.Hierarchy.DescentOrdinarySignedArchiveRead
import OAI.Hierarchy.DescentDatedOrdinaryPostedCut
import OAI.Hierarchy.DescentNamedOrdinaryAdvance
import OAI.Hierarchy.DescentProfiledObservationScalars
import OAI.Hierarchy.DescentNamedShelfWidths

namespace OAI
/-! # The original full archive on the signed input of the selected ordinary date -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
open scoped Fin.CommRing
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] Origin.source Origin.archivePackage issued
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
      (atRound (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).capGain) (positive : 0 < p)
    (room : 10*(X.size+1) ≤ (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : (stageNumbers G t (Nat.log 2 payload/(2*β)) f g rate siteCount (DescentCompiler.TerminalScale.tail τ (Nat.log 2 payload/(2*β)))).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ)
local notation "fee" => ((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)
local notation "pins" => (Σ _ : Fin (S).copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)

open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler.TerminalScale
variable {n₀ δ : ℕ} (board : NonlinearExpanders.Graph n₀ δ) (op : RotorSpec)
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
local notation "geom" i => Geometry G S menu k w i (cursor i)
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
local notation "walk₀" votes => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow votes

open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette DescentOperandStateBanks
local notation "register" i => (cursor i).ports
local notation "time" i => (cursor i).floor
local notation "program" => RegisterTimeline.instruction (w:=w) traces menu initial
local notation "atDate" fn:arg i:arg tick:arg => fn (register i) tick op g frozen p f drift degree payload
  ((menu).seats i) (time i) (menu).ordinary
private abbrev OrdinaryArchiveEntryClaim : Prop := ∀ (K headRate : ℕ)
    (_grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (_purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (_returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (_receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (_growth : drift+1 ≤ scale J₀ driftR) (_sites : siteCount≤(2^payload)^2)
    (_input : p≤payload) (_coeff : degree≤degreeMax) (_original : (S).firstWidth G.b p≤payload)
    (_pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (_headerFits : initial.floor≤2^(headRate*payload)) (_machine : (t+1+max K headRate+2)*payload≤w)
    (_matcher:MatcherRoom G S k p payload)
    (_signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤payload)
    (_palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (_nonempty:0<sockets)
    (_split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (_beforeHeader:lo+extent storage (ch).layout≤header) (_oldHeader:header< initial.floor)
    (votes:(ch).Pin→Bool) (m:Memory w)
    {W:MarkedWorld F 0 pins widths} {i z D z' D':ℕ} {q:ℝ} {nonneg:0≤fee}
    {prior:Reached W G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {T:StageInput W G q fee} {choice:(T.result nonneg).Choice} {n:Normalize ((T.result nonneg).state choice)}
    {next:Reached n.result G price fee S k (i+1) z' D' ((S).epochPower^(S).priceExponent) s}
    (ticket:OrdinaryLink prior nonneg T choice n next)
    (before:Path (trace (walk₀ votes)).origin.source prior) (after:Path next (trace (walk₀ votes)).target)
    (_located:(before.ordinary ticket).append after=(trace (walk₀ votes)).path)
    (_cells:geom i) (B : BitDescription W) (number : Local B)
    (places : DatePorts.RangeRoom (register i) prior B) {R Z : ℕ} (shape : WorldShape p R B)
    (labels : NodeOrder.All B→Label G s Z op) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^(register i).venue.k)→Fin (register i).nodes→Fin (register i).operandHosts→Fin (register i).venue.groups→ℕ)
    (_stored : DatePorts.ArchiveRead (register i) prior B number places shape op labels pointer flags (DateCode.history program m i))
    (_roles : (register i).RoleRows),
    ∃(layout:(atDate DatePorts.OrdinaryCodeRoom i ticket) w)
      (exec:(atDate DatePorts.OrdinaryExecutionRoom i ticket) w ((menu).profile i) header layout),
      program i=(atDate DatePorts.ordinaryDate i ticket) w ((menu).profile i) header positiveK layout ∧
      (register (i+1))=(atDate DatePorts.ordinaryPorts i ticket) ∧
      DateCode.history program m (i+1)=(atDate DatePorts.ordinaryOutput i ticket) w ((menu).profile i) header
        positiveK layout exec (DateCode.history program m i) ∧
      DatePorts.ArchiveRead (register i) prior B number places shape op labels pointer flags
        ((atDate DatePorts.ordinarySignedMemory i ticket) w ((menu).profile i) header positiveK layout exec
          (DateCode.history program m i))

theorem profiled_ordinary_archive_entry :
    OrdinaryArchiveEntryClaim (driftR:=driftR) (ratio:=ratio) X G t rate τ β siteCount payload
      ordinary reset branch positive room shorten w fit board op drift degree degreeMax lo header initial := by
  intro K headRate grant purchase returns receiver growth sites input coeff original pre positiveK headerFits
    machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader votes m W i z D z' D' q
    nonneg prior T choice n next ticket before after located cells B number places R Z shape labels pointer flags
    stored roles
  let evt:RunTrace.Events traces i:=⟨walk₀ votes,.ordinary before ticket after located⟩
  let at_:=cursor i
  let v:=model i at_ ticket
  have dates:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have axis:=dates.2 cells
  have buy:0<v.resolver.lanes ∧ v.fullEnd at_.floor<2^w:=axis.1
  have extra:max (v.fullEnd at_.floor) (v.signedGuard (v.stageStart at_.floor))<2^w:=axis.2
  have word:payload≤w:=(Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine
  have live:i<(S).length:=ticket.hubRows.choose
  have code:=Branch.registered_geometry_fits X G S (trace (walk₀ votes)) ticket before after located op frozen drift
    degree payload at_.floor at_.ports (menu).ordinary board (menu).seats (menu).profile header w live word cells
    cells.degree ⟨rfl,rfl⟩ buy.1 buy.2
  have total:=profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader
    oldHeader i evt cells
  have common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl i at_
  let native:=(atDate DatePorts.ordinaryDate i ticket) w ((menu).profile i) header positiveK code
  let result : RegisterTimeline.Position:=⟨atDate DatePorts.ordinaryPorts i ticket,v.fullEnd at_.floor⟩
  let mv : RegisterTimeline.Move w:=⟨native,result⟩
  have posted : RegisterTimeline.issued traces menu i evt at_ mv:=⟨positiveK,code,rfl⟩
  have seen:=RegisterTimeline.ordinary_posted_cut traces menu initial (walk₀ votes) m before ticket after located
    positiveK code (total code) (fun ev y hy=>common ev evt y mv hy posted)
  refine ⟨code,total code,seen.1,seen.2.1,seen.2.2,?_⟩
  apply DatePorts.ordinary_signed_archive _ ticket op g frozen p f drift degree payload _ _ _ w _ header positiveK
    code (total code) B number places shape labels pointer flags _ stored _ roles
  rw [←places.radix]
  exact cells.archive

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
