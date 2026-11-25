import OAI.Hierarchy.DescentProfiledResetInvoice
import OAI.Hierarchy.DescentRegisteredCalendarPurchase

namespace OAI
/-! Charge the complete original compiler dates to the uniform public purchase. -/
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
open scoped BigOperators
noncomputable section
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
local notation "socket" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin" => NativeBranch.binLimit (k:=cell) S

include boardAt in
theorem profiled_funded_ledger (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (lead exponent saving ordinaryLead ordinaryRate share packing : ℕ)
    (fund : DateBook G board op K ordinaryLead ordinaryRate share saving packing lead exponent τ B h)
    (width : h ≤ p*scale J packing)
    (donors : ∀i < (S).length,∀e : RunTrace.Events traces i,
      ordinaryBill traces b₀ initial (w:=w) i ((S).hostSize i*h*(ordinaryLead*scale J ordinaryRate)+
        (S).hostSize i*((S).groupCount i*(S).radix)*(ordinaryLead*scale J ordinaryRate)+
        share*(copies/(2^J)^saving)) e) :
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces b₀ initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p)) :=by
  exact profiled_ledger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size chosen seed placed
    R H base field wire hist born ratioFit dataFits input ambient lead exponent saving fund.resets
    ordinaryLead ordinaryRate share donors (fund.rows copies p width)

open ThreeFlat.RAM PhysicalProcedure in
include boardAt in
theorem profiled_boot_and_dates (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (lead exponent saving ordinaryLead ordinaryRate share packing : ℕ)
    (fund : DateBook G board op K ordinaryLead ordinaryRate share saving packing lead exponent τ B h)
    (width : h ≤ p*scale J packing)
    (donors : ∀i < (S).length,∀e : RunTrace.Events traces i,
      ordinaryBill traces b₀ initial (w:=w) i ((S).hostSize i*h*(ordinaryLead*scale J ordinaryRate)+
        (S).hostSize i*((S).groupCount i*(S).radix)*(ordinaryLead*scale J ordinaryRate)+
        share*(copies/(2^J)^saving)) e)
    (boot : Procedure w) (ticks : ℕ) :
    let code:=instruction (w:=w) traces b₀ initial
    (DateCode.afterTicks ticks code (S).length+7*DescentStaticWordColumn.names (DateCode.afterBoot boot code (S).length))*w*2^J ≤
      ((ticks+7*DescentStaticWordColumn.names boot)*w)*2^J+2*(copies*((S).copies*p)) :=by
  apply executed_calendar traces b₀ initial boot ticks J copies p
  exact profiled_funded_ledger X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size chosen seed placed
    R H base field wire hist born ratioFit dataFits input ambient lead exponent saving ordinaryLead ordinaryRate share packing
    fund width donors

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
