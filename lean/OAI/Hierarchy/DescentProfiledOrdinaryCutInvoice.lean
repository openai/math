import OAI.Hierarchy.DescentProfiledFundedLedger
import OAI.Hierarchy.DescentProfiledOfferInvoice
import OAI.Hierarchy.DescentNamedProfiledOffer
import OAI.Hierarchy.DescentNamedProfileRoom

namespace OAI
/-! The ordinary invoice uses the signed ticket, register and packed profile at its actual cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale DescentDatedAddressBook PhysicalReset RegisteredReset DescentHostDegree
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open scoped BigOperators
noncomputable section
attribute [local irreducible] issued normalizedPackedChart Origin.source Origin.archivePackage
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F)
    {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g resetCost cut ratio drift driftR bound slots τ B h copies p w lo header limit : ℕ)
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g resetCost copies tb
local notation "cell" => groupBits t J (hostRate t resetCost) (capRate G t g) (cutRate t f g)
local notation "ar" => PitchCalendar.argumentRate G board op t f g resetCost drift driftR bound slots
local notation "rr" => PitchCalendar.roleRate G board op t f g resetCost drift bound slots
local notation "receiver" => degreeRate G board op t f g resetCost (maximumDegree (t+1))
local notation "K" => (⟨t,f,g,resetCost,atRound t,cut,ratio,receiver,drift,bound,max ar rr⟩ : RegisteredReset.Parameters)
variable (ordinary : OrdinaryRates G S cell cut) (reset : ResetRates G S cell (atRound t) n d op.C f g cut tb)
    (boardAt : reset.board=board)
    (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < p) (room : 10*(X.size+1) ≤ copies)
    (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2) (fit : (S).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
local notation "b₀" => fromProfiles G S board op cell tb p f g drift limit h lo header (ch).layout
variable (initial : Position)
local notation "cursor" i:arg => calendar (w:=w) traces b₀ initial i
local notation "socket" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin" => NativeBranch.binLimit (k:=cell) S

local notation "Offers" => ProfiledOrdinaryOffer G f g board op t resetCost τ drift bound B h
local notation "grain" => DescentPackedEpochShelves.grain (h/2) G.C

theorem profiled_ordinary_bill (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (guard : ∀i e,Geometry G S b₀ cell w i (cursor i) →
      profiledGuard X G t resetCost τ B copies h ordinary reset branch positive room shorten w fit
        board op drift limit lo header initial i e < 2^w)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (upperSites : copies ≤ (2^h)^2) (firstWidth : (S).firstWidth G.b p ≤ h)
    (beforeHeader : lo+extent grain (ch).layout ≤ header) (oldHeader : header < initial.floor)
    (lead exponent share saving : ℕ)
    (prices : ∀x : Offers,let sx:=stageNumbers G t J f g resetCost x.slot.sites tb
      0 < x.slot.p → 2^h ≤ x.slot.sites → h ≤ x.slot.bus → x.slot.bus ≤ ratio*h → x.slot.bus+1 ≤ (ratio+1)*h →
      x.HeaderRoom → x.slot.position.ports.ArchivePitchRoom (sx.groupCount x.slot.age) h (scale J ar) (scale J rr) →
      max x.endAt (x.model.signedGuard x.stageFloor) < 2^x.slot.bus →
      ∀(live : 0 < cell) (room : x.CodeRoom),(x.date live room).tariff ≤ x.Price lead exponent share saving)
    (i : ℕ) (e : RunTrace.Events traces i) :
    ordinaryBill traces b₀ initial (w:=w) i ((S).hostSize i*h*(lead*scale J exponent)+
      (S).hostSize i*((S).groupCount i*(S).radix)*(lead*scale J exponent)+share*(copies/(2^J)^saving)) e :=by
  have prior:=profiled_installed X G S ordinary reset branch positive room shorten w fit board op tb drift limit h lo header
    initial seed placed i e
  have protectedAt:=guard i e prior.1
  have plusOne : w+1 ≤ (ratio+1)*h:=by
    rw [Nat.add_mul,Nat.one_mul]
    have ph:=positive.trans_le input
    omega
  obtain ⟨c,e⟩:=e
  cases e with
  | reset before closed after joined=>trivial
  | @ordinary world z D nextZ nextD actualRate src he actualInput ballot normal dst before ticket after joined=>
    let x:=profiled_ordinary_offer X G t resetCost τ B copies h ordinary reset branch positive room shorten w fit
      board op drift limit bound lo header initial upperSites input size firstWidth c (i:=i) (z:=z) (D:=D) (nextZ:=nextZ) (nextD:=nextD)
      (actualRate:=actualRate) (world:=world) (src:=src) (he:=he) (actualInput:=actualInput) (ballot:=ballot)
      (normal:=normal) (dst:=dst) before ticket after joined prior.1
    have buses:=calibrated_prefix_pitch X G S ordinary reset branch positive room shorten w b₀ initial rfl rfl rfl
      slots buy rfl rfl rfl capDrift size chosen seed placed R H base field wire hist born c before
      ((Path.here.ordinary ticket).append after) ((Path.append_cut_assoc before (Path.here.ordinary ticket) after).symm.trans joined)
    obtain ⟨move,emitted,afterFit,_⟩:=prior.2
    have currentFit:=(forward traces b₀ i ⟨c,.ordinary before ticket after joined⟩ (cursor i) move emitted).trans_lt afterFit
    have headerRoom:=registered_profile_room X G S ordinary reset branch positive room shorten w fit board op
      tb drift limit h lo header initial beforeHeader oldHeader c ticket before after joined currentFit
    obtain ⟨_,room₀,rfl⟩:=emitted
    exact prices x positive ambient dataFits ratioFit plusOne headerRoom buses protectedAt

include boardAt in
/-- Charge the ordinary and reset projections on the identical original
compiler and the identical physical cursor at every date. -/
theorem profiled_all_date_ledger (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (guard : ∀i e,Geometry G S b₀ cell w i (cursor i) →
      profiledGuard X G t resetCost τ B copies h ordinary reset branch positive room shorten w fit
        board op drift limit lo header initial i e < 2^w)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (upperSites : copies ≤ (2^h)^2) (firstWidth : (S).firstWidth G.b p ≤ h)
    (beforeHeader : lo+extent grain (ch).layout ≤ header) (oldHeader : header < initial.floor)
    (resetLead resetRate lead exponent share saving packing : ℕ)
    (fund : DateBook G board op K lead exponent share saving packing resetLead resetRate τ B h)
    (packed : h ≤ p*scale J packing)
    (prices : ∀x : Offers,let sx:=stageNumbers G t J f g resetCost x.slot.sites tb
      0 < x.slot.p → 2^h ≤ x.slot.sites → h ≤ x.slot.bus → x.slot.bus ≤ ratio*h → x.slot.bus+1 ≤ (ratio+1)*h →
      x.HeaderRoom → x.slot.position.ports.ArchivePitchRoom (sx.groupCount x.slot.age) h (scale J ar) (scale J rr) →
      max x.endAt (x.model.signedGuard x.stageFloor) < 2^x.slot.bus →
      ∀(live : 0 < cell) (room : x.CodeRoom),(x.date live room).tariff ≤ x.Price lead exponent share saving) :
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces b₀ initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p)) :=by
  apply profiled_funded_ledger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size chosen seed placed
    R H base field wire hist born ratioFit dataFits input ambient resetLead resetRate saving lead exponent share packing
    fund packed
  exact fun i _ e=>profiled_ordinary_bill X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset branch positive room shorten fit initial buy capDrift size chosen seed placed guard
    R H base field wire hist born ratioFit dataFits input ambient upperSites firstWidth beforeHeader oldHeader
    lead exponent share saving prices i e

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
