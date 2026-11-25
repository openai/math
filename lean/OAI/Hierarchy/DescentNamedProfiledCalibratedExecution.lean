import OAI.Hierarchy.DescentNamedProfiledCalendarRate
import OAI.Hierarchy.DescentNamedProfiledExecution
import OAI.Hierarchy.DescentNamedSelectedExecution
import OAI.Hierarchy.DescentNamedProfileRoom
import OAI.Hierarchy.DescentRegisteredReceiverPurchase

namespace OAI
/-! # The profiled calendar executes every issued ordinary step on arbitrary memory -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option cleanup.letToHave false
set_option maxRecDepth 12000
attribute [local irreducible] normalizedPackedChart Origin.source
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

theorem profiled_calibrated_execution (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤payload) (coeff : degree≤degreeMax) (original : (S).firstWidth G.b p≤payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0<sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤header) (oldHeader:header< initial.floor)
    (i:ℕ) (evt:RunTrace.Events traces i) (cells:geom i) : execute i evt:=by
  have atDate:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites
    input coeff original pre positiveK headerFits machine i evt
  have numbers₁:=atDate.2 cells
  obtain ⟨choice,event⟩:=evt
  cases event with
  | reset before ctl after joined=>trivial
  | ordinary before ticket after joined=>
    let pos:=cursor i
    let v:=model i pos ticket
    have budget:0<v.resolver.lanes ∧ v.fullEnd pos.floor<2^w:=numbers₁.1
    have guard:max (v.fullEnd pos.floor) (v.signedGuard (v.stageStart pos.floor))<2^w:=numbers₁.2
    have space:=((v.full_spent pos.floor).1).trans_lt budget.2
    have paid:=registered_profile_room X G S ordinary reset branch positive room shorten w fit board op
      frozen drift degree payload lo header initial beforeHeader oldHeader choice ticket before after joined space
    have bus:payload≤w:=(Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine
    have pn:0<payload:=positive.trans_le input
    have width:w≤w*payload:=Nat.le_mul_of_pos_right _ pn
    have live:i<(S).length:=ticket.hubRows.choose
    obtain ⟨code,total⟩:=Branch.calibrated_execution_room X G S (trace choice) ticket before after joined
      op frozen drift degree payload pos.floor pos.ports (menu).ordinary board (menu).seats (menu).profile header
      w ((menu).profile i) header w cells ⟨rfl,rfl⟩ matcher bus width positiveK (signed i _ live.le)
      budget.1 paid.1 paid.2 (lt_of_le_of_lt (le_max_right ..) guard) budget.2
      purchase palette rfl rfl rfl growth coeff bin sockets nonempty split positive
    intro other
    exact total

theorem profiled_calibrated_instruction (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤payload) (coeff : degree≤degreeMax) (original : (S).firstWidth G.b p≤payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤w)
    (matcher:MatcherRoom G S k p payload)
    (signed:∀i H:ℕ,i≤(S).length→2*((family i H).unit)≤payload)
    (palette:OrdinaryBooks.PrimitiveCalendar G op t f g rate τ β drift degreeMax driftR payload)
    (bin sockets:ℕ) (nonempty:0<sockets)
    (split:p=bin*(payload/(16*((sockets*(G.b^((S).rounds*(S).height)*G.b))*bin))))
    (beforeHeader:lo+extent storage (ch).layout≤header) (oldHeader:header< initial.floor)
    (i:ℕ) : RegisterTimeline.Protected (RegisterTimeline.instruction (w:=w) traces menu initial i) (cursor i).floor header:=by
  have bus:payload≤w:=(Nat.le_mul_of_pos_left _ (by omega:0<t+1+max K headRate+2)).trans machine
  have init:initial.ports.venue.degree=3:=by simpa only [Nat.zero_mod,atRound] using pre.degree
  apply profiled_instruction X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
    payload lo header initial bus positiveK init (receiver.degreeWord w bus) pre _ _ i
  · intro j e geom₁
    exact ((profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input
      coeff original pre positiveK headerFits machine j e).2 geom₁).1
  · exact profiled_calibrated_execution X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
      board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth sites input coeff
      original pre positiveK headerFits machine matcher signed palette bin sockets nonempty split beforeHeader oldHeader

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
