import OAI.Hierarchy.DescentProfiledLastSlice
import OAI.Hierarchy.DescentTerminalLastOverlapPitch
import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentResetSlotIndex
import OAI.Hierarchy.DescentChronologicalFinalEvent

namespace OAI
/-! # The final normalized calendar cursor buys its own packed slice lookup and signed columns -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentTerminalFixedSlices
open DescentPacking.PackedMatch.Local.Stage DescentTerminalSliceShelf DescentSIMDLookup Filter Chronology RegisterTimeline
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F]

structure FinalSliceFields (G : PoweredGadget F) (S : AtomSchedule) (k drift h : ℕ) (P : Phase F) : Prop where
  word : P.digits*(2+3*P.output.argumentSlots)+Nat.clog 2 ((2+3*P.output.argumentSlots)+1)≤h/2
  lookup : DescentTerminalPointerFrame.size (2+3*P.output.argumentSlots) P.digits≤2*2^(h/2)
  blocks : P.output.receiver.blocks=2^k
  hosts : P.output.receiver.hosts=S.hostSize S.length
  groups : P.output.receiver.groups=S.groupCount S.length
  «arguments» : P.output.argumentSlots=S.retainedArgumentsAt G drift
  rawSigned : P.output.venue.next.signedLanes=S.groupCount S.length
  signed : P.output.venue.next.lanes=S.groupCount S.length
  one : chunks (S.groupCount S.length) P.output.venue.next.signedLanes=1
  receiver : chunks P.output.receiver.groups P.output.receiver.lanes=1

variable (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
  (t f g rate τ drift degreeMax β : ℕ)

def LastSliceAt (h : ℕ) : Prop :=
  ∀(v : ProfiledPosition G board op t f g rate τ drift degreeMax β h) (tag : v.IsReset),
    let x:=ResetArea.atCut G board op t f g rate drift degreeMax v tag
    v.age+1=x.sched.length→FinalSliceFields G x.sched x.k drift h x.slicePhase

local notation "σ" => ResetOutput.receiverRate G board op t f g rate (atRound t)
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g rate 0 0)
local notation "κ" => 1+(hostRate t rate+capRate G t g)*(t+1)+8+cutRate t f g

/-- The cutoff is uniform over the chosen ballot, previous position and physical word size. -/
theorem original_last_lookup_cofinal (branch : G.b≤2^(capRate G t g)) (positive : 0<β)
    (lookup : 2*(τ+(σ+α))≤β) (signed : 2*(τ+κ+σ)≤β) :
    ∀ᶠ h:ℕ in atTop,LastSliceAt G board op t f g rate τ drift degreeMax β h :=by
  filter_upwards [ResetArea.last_lookup G board op t f g rate drift degreeMax τ β branch positive lookup,
    PhysicalReset.scheduled_scale G board op t f g rate τ (atRound t) drift β positive branch degreeMax,
    PhysicalReset.eventually_scheduled G board (t:=t) (f:=f) (g:=g) (reset:=rate) (τ:=τ) («σ» := σ) (B:=β) signed]
    with h priced scale₀ final₀
  intro v tag x last
  obtain ⟨word,shelf,blocks,hosts⟩:=priced v tag last
  obtain ⟨out_,base_,_,_,groups,argc⟩:=x.slice_layout last
  have width:=scale₀ v.sites v.age v.p v.degree v.menu.ordinary x.old.venue x.old.operandLanes
    x.old.roleLanes x.inside x.old.io.wire x.old.io.roster v.grainLimit v.degreeLimit x.reached_degree
    v.geometry.capacity v.geometry.format.paid
  obtain ⟨raw,norm,one⟩:=final₀ v.sites v.age v.p drift v.degree v.menu.ordinary op
    (x.sched.firstWidth G.b v.p) (x.sched.grainAt G.b v.p 0) x.old.operandLanes x.old.roleLanes
    x.old.venue x.old.io.wire x.old.io.roster x.inside last v.grainLimit width
  refine ⟨word,shelf,blocks,hosts,groups,argc,raw,norm,one,?_⟩
  change chunks x.slicePhase.output.receiver.groups x.slicePhase.output.venue.next.signedLanes=1
  rw [groups]
  exact one

end
end Hierarchy.DescentSixParty.SeedNamed

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
set_option quotPrecheck false
set_option hygiene false
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
open DescentTerminalFixedSlices DescentSIMDLookup
local notation "finalIndex" => (S).length-1
local notation "atLast" => cursor finalIndex
local notation "physical" => Phase.atPorts G S board k frozen finalIndex p f g drift degree payload (menu).ordinary op
  (atLast).ports (atLast).floor

attribute [local irreducible] issued
set_option maxHeartbeats 1200000
set_option maxRecDepth 6144
/-- The terminal lookup belongs to the original published menu on every normalized candidate. -/
theorem original_last_lookup
    (sites : siteCount≤(2^payload)^2) (grain : p≤payload) (coeff : degree≤degreeMax)
    (seed : Geometry G S menu k w 0 initial)
    (placed : ∀i (e:RunTrace.Events traces i), RegisterTimeline.fitsAt traces menu initial (w:=w) i e)
    (walk : (last).Choice) (receipt : Path.FinalReset p (trace walk).path)
    (bought : LastSliceAt G board op t f g rate τ drift degreeMax β payload) :
    FinalSliceFields G S k drift payload physical :=by
  have finalReset : Path.FinalReset p (traces walk).path := by
    dsimp only [traceAt]
    exact receipt
  let event : RunTrace.Events traces finalIndex := ⟨walk, Path.FinalReset.event (i := (S).length) finalReset⟩
  have acquired:=profiled_installed X G S ordinary reset branch positive room shorten w fit board op frozen
    drift degree payload lo header initial seed placed finalIndex event
  have closed : finalIndex+1=(S).length:=Path.FinalReset.succ_age (i := (S).length) finalReset
  let v : ProfiledPosition G board op t f g rate τ drift degreeMax β payload:={
    owners:=(ch).Pin, entries:=(ch).layout, sites:=siteCount, p:=p, degree:=degree, lo:=lo,
    header:=header, bus:=w, age:=finalIndex, position:=atLast, siteLimit:=sites, grainLimit:=grain,
    degreeLimit:=coeff, active:=by omega, geometry:=acquired.1}
  have stamp : ((kindCalendar (S).rounds (S).height).drop finalIndex).head?=some true:=by
    have kinds : (traces walk).path.kinds = kindCalendar (S).rounds (S).height := by
      dsimp only [traceAt]
      exact (trace walk).kinds
    rw [←kinds,←Path.FinalReset.is_reset (i := (S).length) finalReset]
    exact (Path.FinalReset.event (i := (S).length) finalReset).shown
  have hit : v.IsReset:=reset_slot_index (S).rounds (S).height finalIndex stamp
  exact bought v hit closed

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
