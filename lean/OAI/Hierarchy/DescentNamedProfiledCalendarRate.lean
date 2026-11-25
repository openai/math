import OAI.Hierarchy.DescentNamedProfiledOffer
import OAI.Hierarchy.DescentProfiledDateSpanBudget
import OAI.Hierarchy.DescentRegisteredReceiverPurchase

namespace OAI
/-! # Uniform admission and signed-read addresses for the concrete named calendar -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
set_option hygiene false
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
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) a.floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 400000
attribute [local irreducible] Origin.source Origin.archivePackage issued traceAt

local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "offer" => ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload
local notation "slot" => ProfiledPosition G board op t f g rate τ drift degreeMax β payload

local notation "guardAt" => profiledGuard X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree lo header initial
local notation "geom" i:arg => Geometry G S menu k w i (cursor i)
local notation "numbers" => profiledNumbers X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "baseRate" => (NativePitch.FundedBase.public_rate G t f g rate).choose
open Filter
namespace ProfiledRate
/-- One exponent covers the actual signed read tests as well as the advancing
address for every ordinary or reset offer at a fixed payload length. -/
def Covers {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
    (op : RotorSpec) (t f g rate τ drift degreeMax β payload K : ℕ) : Prop :=
  (∀x : ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload,
    max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor≤2^(K*payload)) ∧
  ∀x : ProfiledPosition G board op t f g rate τ drift degreeMax β payload,
    x.IsReset→x.resetEnd-x.position.floor≤2^(K*payload)

theorem available (slack : SignedStage.unitRate G t f g rate<β) (branchFit : G.b≤2^(capRate G t g))
    (tailRoom : τ≤β) (cutBought : 2*(1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g)≤β)
    (receiverBought : 2*degreeRate G board op t f g rate (maximumDegree (t+1))≤β) :
    ∃K:ℕ,∀ᶠ h:ℕ in atTop,Covers G board op t f g rate τ drift degreeMax β h K :=
  profiled_span_budget G board op t f g rate τ drift degreeMax β slack branchFit tailRoom cutBought receiverBought
/-- This threshold covers the native calendar, the signed ordinary lookup, and
the reset receiver's address interval before the word multiplier is chosen. -/
def threshold {F₀ : Type} [Field F₀] (gadget : PoweredGadget F₀) {n d : ℕ}
    (graph : NonlinearExpanders.Graph n d) (rotor : RotorSpec)
    (rounds f g rate τ drift driftR degree quota : ℕ) :=
  max (PitchCalendar.threshold gadget graph rotor rounds f g rate drift driftR degree quota τ)
    (max (SignedStage.unitRate gadget rounds f g rate+1)
      (2*(1+(hostRate rounds rate+capRate gadget rounds g)*(rounds+1)+8+cutRate rounds f g)))

/-- The address exponent is fixed before the word-to-payload ratio. The same
sufficiently large payload then has the original seed, operand and return rates. -/
theorem purchased (driftR quota : ℕ) (openTail : 0<τ)
    (fund : threshold G board op t f g rate τ drift driftR degreeMax quota≤β) :
    ∃ K : ℕ,∀ ratio : ℕ,∀ᶠ payload : ℕ in atTop,
      Covers G board op t f g rate τ drift degreeMax β payload K ∧
      PitchCalendar.Purchased G board op t f g rate drift driftR degreeMax quota ratio τ β payload ∧
      ReceiverCalendar G board op t f g rate τ drift degreeMax β payload :=by
  unfold threshold at fund
  have lower : PitchCalendar.threshold G board op t f g rate drift driftR degreeMax quota τ≤β:=by omega
  have unit : SignedStage.unitRate G t f g rate<β:=by omega
  have cutPaid : 2*(1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g)≤β:=by omega
  have branches : G.b≤2^(capRate G t g):=
    (show G.b≤capRate G t g by unfold capRate; omega).trans Nat.lt_two_pow_self.le
  have costs:=lower
  unfold PitchCalendar.threshold at costs
  have tailSmall : τ≤β:=by omega
  have near : 2*degreeRate G board op t f g rate (maximumDegree (t+1))≤β:=by omega
  obtain ⟨K,uniform⟩:=profiled_span_budget G board op t f g rate τ drift degreeMax β unit branches tailSmall cutPaid near
  refine ⟨K,?_⟩
  intro ratio
  filter_upwards [uniform,PitchCalendar.eventually_purchased G board op t f g rate drift driftR degreeMax quota
    ratio τ β openTail lower,paid_receiver_calendar G board op t f g rate τ drift driftR degreeMax quota β lower]
    with payload addr paid ready
  exact ⟨addr,paid,ready⟩

end ProfiledRate

variable {driftR ratio : ℕ}
local notation "funds" => 44*argumentDigitRate G t f g rate driftR baseRate

set_option maxRecDepth 4096 in
theorem profiled_calendar_at_rate (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤payload) (coeff : degree≤degreeMax) (original : (S).firstWidth G.b p≤payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤w)
    (i : ℕ) (e : RunTrace.Events traces i) :
    fitsAt traces menu initial (w:=w) i e ∧ (geom i → numbers i e ∧ guardAt i e<2^w):=by
  let B:=max K headRate
  have powK : 2^(K*payload)≤2^(B*payload):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left ..))
  have head : initial.floor≤2^(B*payload):=headerFits.trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right ..)))
  have bound : (S).length≤2^((t+1)*payload):=by
    have depth : J₀≤payload:=(Nat.div_le_self ..).trans (Nat.log_le_self 2 payload)
    exact (Nat.mul_le_mul_left (t+1) depth).trans (show (t+1)*payload<2^((t+1)*payload) from Nat.lt_two_pow_self).le
  have regular (x : offer):max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor≤2^(B*payload):=
    (grant.1 x).trans powK
  have fresh (x : slot) (tag : x.IsReset) : x.resetEnd-x.position.floor≤2^(B*payload):=(grant.2 x tag).trans powK
  have spans:=profiled_offer_spans X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    board op drift degree degreeMax lo header initial sites input coeff original (2^(B*payload)) regular fresh
  have factor : 0<t+1+B+2:=by omega
  have word : payload≤w:=(Nat.le_mul_of_pos_left _ factor).trans machine
  have admit:=profiled_numbers_from_spans X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial purchase returns receiver rfl rfl rfl growth coeff input original
    word positiveK pre (t+1) B bound head machine (fun j d active=>(spans j d active).1)
  refine ⟨(admit i e).1,?_⟩
  intro geo
  exact ⟨(admit i e).2 geo,profiled_guard_before X G t rate τ β siteCount payload ordinary reset branch positive
    room shorten w fit board op drift degree degreeMax lo header initial sites input coeff original (t+1) B bound head
    machine pre regular fresh i e geo (fun j _ d=>(admit j d).1)⟩

set_option maxRecDepth 4096 in
theorem profiled_last_floor_at_rate (K headRate : ℕ)
    (grant : ProfiledRate.Covers G board op t f g rate τ drift degreeMax β payload K)
    (purchase : ArgumentCalendar G op t f g rate τ β drift driftR degreeMax payload)
    (returns : ReturnCalendar G t f g rate driftR funds τ β ratio payload)
    (receiver : ReceiverCalendar G board op t f g rate τ drift degreeMax β payload)
    (growth : drift+1 ≤ scale J₀ driftR) (sites : siteCount≤(2^payload)^2)
    (input : p≤payload) (coeff : degree≤degreeMax) (original : (S).firstWidth G.b p≤payload)
    (pre : Geometry G S menu k w 0 initial) (positiveK : 0<k)
    (headerFits : initial.floor≤2^(headRate*payload)) (machine : (t+1+max K headRate+2)*payload≤w)
    : (cursor (S).length).floor<2^((t+1+max K headRate+2)*payload):=by
  let B:=max K headRate
  have cap : 2^(K*payload)≤2^(B*payload):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_left ..))
  have head := headerFits.trans (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.mul_le_mul_right payload (le_max_right K headRate)))
  have length_ : (S).length≤2^((t+1)*payload):=by
    have depth : J₀≤payload:=(Nat.div_le_self ..).trans (Nat.log_le_self 2 payload)
    exact (Nat.mul_le_mul_left (t+1) depth).trans Nat.lt_two_pow_self.le
  have spans:=profiled_offer_spans X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    board op drift degree degreeMax lo header initial sites input coeff original (2^(B*payload))
    (fun x=>(grant.1 x).trans cap) (fun x hit=>(grant.2 x hit).trans cap)
  have accepted:=profiled_calendar_at_rate X G t rate τ β siteCount payload ordinary reset branch positive room
    shorten w fit board op drift degree degreeMax lo header initial K headRate grant purchase returns receiver growth
    sites input coeff original pre positiveK headerFits machine
  change (RegisterTimeline.position (RegisterTimeline.issued (w:=w) traces menu) initial (S).length).floor<_
  rw [position_floor]
  apply within_word (positive.trans_le input) _ head length_
  intro j hj
  apply span_of_issued (ι:=fun _=>Unit) (w:=fun _=>w) (Cut:=fun _ _ i=>RunTrace.Events traces i)
    (h:=0) (i:=()) (fun _ _=>RegisterTimeline.issued (w:=w) traces menu) (fun _ _=>initial)
  intro evt move taken
  have geo:=(profiled_installed X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial pre (fun i e=>(accepted i e).1) j evt).1
  rw [profiled_end_of_issue X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial j evt move taken]
  exact (spans j evt geo).1


end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
