import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentNamedProfileOnCPU
import OAI.Hierarchy.DescentDatedSignedSpace
import OAI.Hierarchy.DescentResetSlotIndex

namespace OAI
/-! # Actual named calendar events as the offered reset or ordinary program -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F : Type} [Field F] {cp nP : ℕ} (X : Catalyst.Approximation F cp nP) (G : PoweredGadget F)
variable {n h C f g p cut tail : ℕ}
variable (t rate τ β siteCount payload : ℕ)
local notation "J₀" => Nat.log 2 payload/(2*β)
set_option quotPrecheck false
local notation "frozen" => DescentCompiler.TerminalScale.tail τ J₀
local notation "S" => stageNumbers G t J₀ f g rate siteCount frozen
local notation "k" => groupBits t J₀ (hostRate t rate) (capRate G t g) (cutRate t f g)
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound (S).rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^(S).capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ (S).initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^(S).rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => (S).firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : s < 2^w)
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
  DatePorts.ordinaryModel (a:RegisterTimeline.Position).ports tick op g frozen p f drift degree payload ((menu).seats i) (a).floor (menu).ordinary
local notation "resetAt" => fun i (a:RegisterTimeline.Position)=>
  PhysicalReset.scheduledAtPorts G S board k frozen i p f g drift degree payload (menu).ordinary op
    ((S).firstWidth G.b p) ((S).grainAt G.b p 0) a.ports a.floor
set_option maxHeartbeats 1400000
set_option maxRecDepth 12000

local notation "roof" => profiledEnd X G S ordinary reset branch positive room shorten w fit board op frozen drift degree payload lo header initial
local notation "offer" => ProfiledOrdinaryOffer G f g board op t rate τ drift degreeMax β payload
local notation "slot" => ProfiledPosition G board op t f g rate τ drift degreeMax β payload

/-- The optional larger signed-read envelope uses the same funded model and
stage start as the native ordinary code. -/
def profiledGuard (i : ℕ) (evt : RunTrace.Events traces i) : ℕ:=by
  let old:=cursor i
  obtain ⟨c,e⟩:=evt
  cases e with
  | ordinary before tick after joined=>
    let v:=model i old tick
    exact max (v.fullEnd old.floor) (v.signedGuard (v.stageStart old.floor))
  | reset before ctl after joined=>exact (resetAt i old).fullEnd

local notation "guardAt" => profiledGuard X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit board op drift degree lo header initial

variable (sites : siteCount≤(2^payload)^2) (input : p≤payload) (coeff : degree≤degreeMax)
    (width : (S).firstWidth G.b p≤payload)

include sites input coeff width in
/-- The original ordinary ticket and both pieces of its history remain visible
in the offer, so the issuing and the pricing theorems use exactly the same program. -/
def profiled_ordinary_offer (c : (last).Choice) {i z D nextZ nextD : ℕ} {actualRate : ℝ}
    {world : MarkedWorld F 0 pins widths}
    {src : Reached world G price fee S k i z D ((S).epochPower^(S).priceExponent) s}
    {actualInput : StageInput world G actualRate fee} {he : 0 ≤ fee}
    {ballot : (actualInput.result he).Choice} {normal : Normalize ((actualInput.result he).state ballot)}
    {dst : Reached normal.result G price fee S k (i+1) nextZ nextD ((S).epochPower^(S).priceExponent) s}
    (a : Path (trace c).origin.source src) (tick : OrdinaryLink src he actualInput ballot normal dst)
    (b : Path dst (trace c).target) (joined : (a.ordinary tick).append b=(trace c).path)
    (geom : Geometry G S menu k w i (cursor i)) : offer :=by
  have live : i < (S).length:=by have lim:=b.kinds_length;omega
  let position : slot:={
    owners:=(ch).Pin, entries:=(ch).layout, sites:=siteCount, p:=p, degree:=degree, lo:=lo,
    header:=header, bus:=w, age:=i, position:=cursor i, siteLimit:=sites, grainLimit:=input,
    degreeLimit:=coeff, active:=live, geometry:=geom}
  let chosen : OrdinaryCut G S k i p f g:={
    copies:=cp, inputs:=nP, original:=X, n:=n, degree:=h, C:=C, R:=max 1 (max reset.bitsR (C*reset.bitsR)),
    price_nonnegative:=by positivity, fee_nonnegative:=by positivity, radix:=ordinary.radix, «run»:=(cert).choose,
    selection:=c, branch:=trace c, world:=world, sourceGrain:=z, sourceDegree:=D,
    source:=src, rate:=actualRate, input:=actualInput, nonnegative:=he, choice:=ballot, norm:=normal,
    targetGrain:=nextZ, targetDegree:=nextD, target:=dst, ticket:=tick, before:=a, after:=b, joined:=joined}
  refine ⟨position,chosen,?_,width⟩
  obtain ⟨sl,_,located,row,_⟩:=registered_profile_exists X G S ordinary reset branch positive room shorten
    w fit payload lo c tick a b joined
  have same:=RegisterTimeline.fromProfiles_at G S board op k frozen p f g drift degree payload
    lo header (ch).layout i sl located
  have capacity:=(normalized_shelf_widths X G S ordinary reset branch positive room shorten w fit
    sl.src (List.mem_of_getElem? row)).2
  exact same.2.1.le.trans capacity


attribute [local irreducible] issued normalizedPackedChart Origin.source Origin.archivePackage

include sites input coeff width in
theorem profiled_offer_at (i : ℕ) (evt : RunTrace.Events traces i)
    (geom : Geometry G S menu k w i (cursor i)) :
    (∃x : offer,x.slot.position=cursor i ∧ x.slot.age=i ∧
      roof i evt=x.endAt ∧ guardAt i evt=max x.endAt (x.model.signedGuard x.stageFloor)) ∨
    (∃x : slot,x.IsReset ∧ x.position=cursor i ∧ x.age=i ∧
      roof i evt=x.resetEnd ∧ guardAt i evt=x.resetEnd):=by
  have live : i<(S).length:=by
    obtain ⟨c,e⟩:=evt
    cases e with
    | ordinary a tick b h=>have lim:=b.kinds_length; omega
    | reset a ctl b h=>have lim:=b.kinds_length; omega
  let position : slot:={
    owners:=(ch).Pin, entries:=(ch).layout, sites:=siteCount, p:=p, degree:=degree, lo:=lo,
    header:=header, bus:=w, age:=i, position:=cursor i, siteLimit:=sites, grainLimit:=input,
    degreeLimit:=coeff, active:=live, geometry:=geom}
  obtain ⟨c,e⟩:=evt
  cases e with
  | @ordinary world z D nextZ nextD actualRate src he actualInput ballot normal dst a tick b joined=>
    let pick:=profiled_ordinary_offer X G t rate τ β siteCount payload ordinary reset branch positive room shorten
      w fit board op drift degree degreeMax lo header initial sites input coeff width c
      (i:=i) (z:=z) (D:=D) (nextZ:=nextZ) (nextD:=nextD) (actualRate:=actualRate) (world:=world)
      (src:=src) (he:=he) (actualInput:=actualInput) (ballot:=ballot) (normal:=normal) (dst:=dst) a tick b joined geom
    exact Or.inl ⟨pick,rfl,rfl,rfl,rfl⟩
  | reset a ctl b joined=>
    let hit : (trace c).path.Event i:=.reset a ctl b joined
    have tagged : ((kindCalendar (S).rounds (S).height).drop i).head?=some true:=by
      rw [←(trace c).kinds]
      exact hit.shown
    exact Or.inr ⟨position,reset_slot_index (S).rounds (S).height i tagged,rfl,rfl,rfl,rfl⟩

include sites input coeff width in
theorem profiled_offer_spans (bound:ℕ)
    (regular : ∀x:offer,max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor≤bound)
    (fresh : ∀x:slot,x.IsReset→x.resetEnd-x.position.floor≤bound)
    (i : ℕ) (evt : RunTrace.Events traces i) (geom : Geometry G S menu k w i (cursor i)) :
    roof i evt-(cursor i).floor≤bound ∧ guardAt i evt-(cursor i).floor≤bound:=by
  rcases profiled_offer_at X G t rate τ β siteCount payload ordinary reset branch positive room shorten w fit
    board op drift degree degreeMax lo header initial sites input coeff width i evt geom with
    ⟨x,atPos,_,endAt,guardEq⟩ | ⟨x,kind,atPos,_,endAt,guardEq⟩
  · rw [←atPos,endAt,guardEq]
    exact ⟨(Nat.sub_le_sub_right (le_max_left ..) _).trans (regular x),regular x⟩
  · rw [←atPos,endAt,guardEq]
    exact ⟨fresh x kind,fresh x kind⟩


include sites input coeff width in
/-- The optional signed-read guard fits the common physical address word even
at the first offered event that has yet to run. -/
theorem profiled_guard_before (A B : ℕ)
    (stages : (S).length≤2^(A*payload)) (head : initial.floor≤2^(B*payload)) (bus : (A+B+2)*payload≤w)
    (seed : Geometry G S menu k w 0 initial)
    (regular : ∀x:offer,max x.endAt (x.model.signedGuard x.stageFloor)-x.slot.position.floor≤2^(B*payload))
    (fresh : ∀x:slot,x.IsReset→x.resetEnd-x.position.floor≤2^(B*payload))
    (i : ℕ) (evt : RunTrace.Events traces i) (geom : Geometry G S menu k w i (cursor i))
    (previous : ∀ j < i, ∀e:RunTrace.Events traces j,fitsAt traces menu initial (w:=w) j e) :
    guardAt i evt<2^w:=by
  have spans:=profiled_offer_spans X G t rate τ β siteCount payload ordinary reset branch positive room shorten
    w fit board op drift degree degreeMax lo header initial sites input coeff width (2^(B*payload)) regular fresh
  exact (profiled_address_before X G S ordinary reset branch positive room shorten w fit board op frozen drift degree
    payload lo header initial seed A B (positive.trans_le input) stages head (fun j e h=>(spans j e h).1)
    i evt previous (guardAt i evt) (spans i evt geom).2).trans_le (Nat.pow_le_pow_right (by decide) bus)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
