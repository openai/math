import OAI.Hierarchy.DescentProfiledOrdinaryCutInvoice
import OAI.Hierarchy.DescentRegisteredPackingWidth
import OAI.Hierarchy.DescentNamedProfiledCalendarRate

namespace OAI
/-! The public calendar rate pays the date addresses and signed guards on the
same execution that the native stage ledger prices. -/
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
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall
open scoped BigOperators
noncomputable section
private theorem calibrated_group_pos (t J hg cg cut : ℕ) : 0 < groupBits t J hg cg cut := by
  unfold groupBits
  omega

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

include boardAt in
theorem profiled_calendar_ledger (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial)
    (addrRate headRate : ℕ) (address : ProfiledRate.Covers G board op t f g resetCost τ drift bound B h addrRate)
    (headFit : initial.floor ≤ 2^(headRate*h)) (machineFit : (t+1+max addrRate headRate+2)*h ≤ w)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (ambient : 2^h ≤ copies)
    (upperSites : copies ≤ (2^h)^2)
    (beforeHeader : lo+extent grain (ch).layout ≤ header) (oldHeader : header < initial.floor)
    (resetLead resetRate lead exponent share saving : ℕ)
    (fund : DateBook G board op K lead exponent share saving (5+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))) resetLead resetRate τ B h)
    (prices : ∀x : Offers,let sx:=stageNumbers G t J f g resetCost x.slot.sites tb
      0 < x.slot.p → 2^h ≤ x.slot.sites → h ≤ x.slot.bus → x.slot.bus ≤ ratio*h → x.slot.bus+1 ≤ (ratio+1)*h →
      x.HeaderRoom → x.slot.position.ports.ArchivePitchRoom (sx.groupCount x.slot.age) h (scale J ar) (scale J rr) →
      max x.endAt (x.model.signedGuard x.stageFloor) < 2^x.slot.bus →
      ∀(live : 0 < cell) (room : x.CodeRoom),(x.date live room).tariff ≤ x.Price lead exponent share saving) :
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces b₀ initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p)) :=by
  obtain ⟨input,original,packed⟩:=registered_packing_width G t J f g resetCost copies τ h p positive chosen
  have active : 0 < cell := calibrated_group_pos ..
  have bus : h ≤ w:=(Nat.le_mul_of_pos_left _ (by omega : 0 < t+1+max addrRate headRate+2)).trans machineFit
  have ready:=profiled_calendar_at_rate X G t resetCost τ B copies h ordinary reset branch positive room shorten
    w fit board op drift limit bound lo header initial addrRate headRate address buy.old buy.returned lookups
    capDrift upperSites input size original seed active headFit machineFit
  exact profiled_all_date_ledger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size chosen
    seed (fun i e=>(ready i e).1) (fun i e geo=>((ready i e).2 geo).2)
    R H base field wire hist born ratioFit bus input ambient upperSites original beforeHeader oldHeader
    resetLead resetRate lead exponent share saving _ fund packed prices

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
