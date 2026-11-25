import OAI.Hierarchy.DescentRegisteredResetCutPrice
import OAI.Hierarchy.DescentCalibratedPrefixPitch
import OAI.Hierarchy.DescentNamedProfiledNumbers
import OAI.Hierarchy.DescentRegisteredReceiverPurchase

namespace OAI
open private source_cap from OAI.Hierarchy.DescentNamedOrdinaryCode

/-! Project every reset charge at the original normalized compiler cursor, with
both pitches from the genuine initial selector and its subsequent register moves. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "digits" => S.initialDigits ordinary.radix
local notation "q" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)

local notation "actual" => issued X G S ordinary reset branch positive room shorten
local notation "price" => S.epochPower^S.priceExponent
local notation "epsilon" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
attribute [local irreducible] SeedNamed.issued Origin.source
set_option maxRecDepth 12000

private theorem original_calendar_data (c : (last).Choice) : (traces c).path.capFactors = capCalendar G.b S.rounds g S.height ∧
    (traces c).first.placement.cap = 256 ∧ (traces c).firstDegree = 3 ∧
    (traces c).path.kinds = kindCalendar S.rounds S.height := by
  dsimp only [SeedNamed.traceAt]
  refine ⟨(actual c).calendar, ?_, rfl, (actual c).kinds⟩
  let o := (actual c).origin
  have capResult := source_cap o
  exact capResult

end
end Hierarchy.DescentSixParty.SeedNamed

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
set_option maxHeartbeats 1500000
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
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
local notation "b₀" => fromProfiles G S board op cell tb p f g drift limit h lo header (ch).layout
variable (initial : Position)
local notation:max "cursor" i:arg => calendar (w:=w) traces b₀ initial i
local notation "socket" => 2^Nat.clog 2 (NativeBranch.localLimit G S)
local notation "bin" => NativeBranch.binLimit (k:=cell) S

attribute [local irreducible] SeedNamed.issued Origin.source

include boardAt in
theorem profiled_reset_bill (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (lead exponent saving : ℕ)
    (price : ∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
      a.code.tariff ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+a.copies/(2^J)^saving)
    (i : ℕ) (live : i < (S).length) (event : RunTrace.Events traces i) :
    resetBill traces b₀ initial (w:=w) i ((S).hostSize i*h*(lead*scale J exponent)+
      (S).hostSize i*((S).groupCount i*(S).radix)*(lead*scale J exponent)+copies/(2^J)^saving) event :=by
  have geo:=profiled_installed X G S ordinary reset branch positive room shorten w fit board op tb drift limit h lo header
    initial seed placed i event
  let old:=(cursor i).ports
  have priorDegree:old.venue.degree ≤ maximumDegree (t+1) :=geo.1.degree.le.trans (round_degree_le t i)
  have lookup:=lookups.measured copies i p limit b₀ old rfl rfl rfl rfl rfl rfl rfl rfl rfl
    input size priorDegree geo.1.capacity geo.1.format.paid
  have widthAt := (b₀).receiverWidth_at G S cell i old (old.priorStart cell (cursor i).floor)
  have selectedRoom := (Nat.mul_le_mul_left 8 widthAt.le).trans lookup.1
  have selectedScale := widthAt.le.trans lookup.2
  have word:old.venue.degree+1 < 2^w:=(Nat.succ_le_succ priorDegree).trans_lt (lookups.degreeWord w dataFits)
  have standard (j : ℕ) (_hj : j < (S).length) (_ordinary : j%(t+1)≠t):
      ((b₀).ordinary j).payload=h ∧ ((b₀).ordinary j).unit=(DonorDate.atDate G S g cell j p).amount:=⟨rfl,rfl⟩
  have next:=(buy.returned.rows copies p (i+1) 1 (b₀).ordinary input standard).1
  have chartData := original_calendar_data X G S ordinary reset branch positive room shorten
  let issuedWidth := (S).firstWidth G.b p
  let portIndex := (Σ _ : Fin (S).copies, Fin (Fintype.card (Port nP X.width)))
  let certificate := SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
  let choices := (Epochs.finish G _ _ certificate.choose).Choice
  have billedAt := trace_reset_bill (P:=portIndex) (d₀:=0) (bits:=fun _ : portIndex => issuedWidth*1)
    (wire:=(S).epochPower^(S).priceExponent) (hist:=issuedWidth) (final:=(S).length)
    (q:=(1/((issuedWidth:ℝ)*((S).epochPower^(S).priceExponent:ℝ)):ℝ))
    (ε:=((((S).initialSites*(S).copies:ℕ):ℝ)/(S).epochPower)) (C:=choices) G board op K τ B h copies p w limit (b₀).ordinary (b₀).seats (b₀).profile header
    traces initial i reset boardAt lead exponent saving price rfl (fun c => (chartData c).1)
    (fun c => (chartData c).2.1) (fun c => (chartData c).2.2.1) (fun c => (chartData c).2.2.2) live geo.1 size input ambient
    ratioFit dataFits word standard next
  obtain ⟨c,ev⟩:=event
  cases ev with
  | ordinary before ticket after joined=>trivial
  | @reset U z D _ _ _ _ _ _ _ src ctl before stage after cutHere=>
    let tailPath := (Path.here.reset stage).append after
    have joined := (Path.append_cut_assoc before (Path.here.reset stage) after).symm.trans cutHere
    have bus:=calibrated_prefix_pitch X G S ordinary reset branch positive room shorten w b₀ initial rfl rfl rfl
      slots buy rfl rfl rfl capDrift size chosen seed placed R H base field wire hist born c (U:=U) (i:=i) (z:=z) (D:=D) (r:=src) (by dsimp only [SeedNamed.traceAt] at before; exact before)
      (by dsimp only [SeedNamed.traceAt] at tailPath; exact tailPath)
      (by dsimp only [SeedNamed.traceAt] at joined; exact joined)
    have density:=bus.toArchiveDensity.weaken
      (short_mono J (Nat.le_max_left ar rr)) (short_mono J (Nat.le_max_right ar rr))
    obtain ⟨move,hit,roof,small⟩:=geo.2
    obtain ⟨capacity,space,rfl⟩:=hit
    exact billedAt density (fun _=>⟨selectedRoom,selectedScale,roof⟩)
      ⟨c,.reset before stage after cutHere⟩

include boardAt in
/-- Dated work through the actual last reset of the original normalized compiler.
The subsequent replay has its own separately purchased native code. -/
theorem profiled_ledger (buy : PitchCalendar.Purchased G board op t f g resetCost drift driftR bound slots ratio τ B h)
    (lookups : ReceiverCalendar G board op t f g resetCost τ drift bound B h)
    (capDrift : drift+1 ≤ scale J driftR) (size : limit ≤ bound)
    (chosen : p=bin*(h/(16*((socket*(G.b^(t*J)*G.b))*bin))))
    (seed : Geometry G S b₀ cell w 0 initial) (placed : ∀i e,fitsAt traces b₀ initial (w:=w) i e)
    (R H base field wire hist : ℕ)
    (born : initial.ports=DatePorts.initial G op X R
      (DescentDatedSeedStartup.selectedLayout G S h cell tb g p drift limit f slots base field wire hist)
      cell H ((S).groupCount 0) h ((S).grainAt G.b p 0))
    (ratioFit : w ≤ ratio*h) (dataFits : h ≤ w) (input : p ≤ h) (ambient : 2^h ≤ copies)
    (lead exponent saving : ℕ)
    (price : ∀a : Sample G board op K τ B h,a.Geometry→a.ReachedAt→
      a.code.tariff ≤ a.hostWork*(lead*scale J exponent)+a.groupWork*(lead*scale J exponent)+a.copies/(2^J)^saving)
    (ordinaryLead ordinaryRate share : ℕ)
    (donors : ∀i < (S).length,∀e : RunTrace.Events traces i,
      ordinaryBill traces b₀ initial (w:=w) i ((S).hostSize i*h*(ordinaryLead*scale J ordinaryRate)+
        (S).hostSize i*((S).groupCount i*(S).radix)*(ordinaryLead*scale J ordinaryRate)+
        share*(copies/(2^J)^saving)) e)
    (book : let price:=((max lead ordinaryLead)+(max 1 share)+137*ratio)*scale J (max exponent ordinaryRate)
      (((S).length+1)*(price+1))*h ≤ p*2^tb ∧ ((S).length+1)*(2^(S).hostGain)^(S).length*price*2^J ≤ p) :
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces b₀ initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p)) :=by
  have sites:=Nat.lt_of_lt_of_le (Nat.two_pow_pos h) ambient
  have hp:=positive.trans_le input
  apply paid_calendar traces b₀ initial t J f g resetCost copies τ h ratio p
    (max lead ordinaryLead) (max exponent ordinaryRate) (max 1 share) saving rfl hp sites ratioFit _ book
  intro i hi e fee
  have orig:=donors i hi e
  have calibrated:=profiled_reset_bill X G board op t f g resetCost cut ratio drift driftR bound slots τ B h copies p w
    lo header limit ordinary reset boardAt branch positive room shorten fit initial buy lookups capDrift size chosen seed placed
    R H base field wire hist born ratioFit dataFits input ambient lead exponent saving price i hi e
  have old:=date_quote_mono ((S).hostSize i) ((S).groupCount i*(S).radix) h (copies/(2^J)^saving) J
    ordinaryLead ordinaryRate share (max lead ordinaryLead) (max exponent ordinaryRate) (max 1 share) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have new_:=date_quote_mono ((S).hostSize i) ((S).groupCount i*(S).radix) h (copies/(2^J)^saving) J
    lead exponent 1 (max lead ordinaryLead) (max exponent ordinaryRate) (max 1 share) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  exact ⟨ordinaryBill_mono traces b₀ initial e old orig,
    resetBill_mono traces b₀ initial e new_ (by simpa only [Nat.one_mul] using calibrated)⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
