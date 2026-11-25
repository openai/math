import OAI.Hierarchy.DescentNormalizedSeedFences
import OAI.Hierarchy.DescentNormalizedSeedEntry
import OAI.Hierarchy.DescentCalendarWordPurchase

namespace OAI
/-! Exact price of the dated instructions starting at the registered original seed. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale DescentDatedAddressBook PhysicalReset RegisteredReset DescentHostDegree
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall DescentWideSeedFlags
open scoped BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g resetCost drift bound : ℕ)
  (τ B h copies H degree wire hist cut w : ℕ)
set_option hygiene false
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G t J f g resetCost copies tb
local notation "k" => groupBits t J (hostRate t resetCost) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h
local notation "W" => NativeBranch.binLimit («k»:=k) S
local notation "q" => headArity G S
variable {cp nP : ℕ} (X : Approximation F cp nP) (ordinary : OrdinaryRates G S k cut)
  (reset : ResetRates G S k (atRound t) n d op.C f g cut tb)
  (branch : G.b ≤ 2^(capRate G t g)) (positive : 0 < p) (room : 10*(X.size+1) ≤ copies)
  (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2) (fit : (S).firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "bins" => terminalBinCount X G S p q W n d op.C f g+1
local notation "raw" => terminalRawRows X G S p q n d op.C f g
local notation "v" => originalSeedHead G op drift X (ch).layout S k tb h H degree wire hist bins raw
local notation "lo" => selectorBase X (S).copies ((v).width G) h (ch).layout.length
local notation "header" => (v).base G h-1
local notation "menu" => fromProfiles G S board op k tb p f g drift degree h lo header (ch).layout
local notation "initial" => (v).position G op t f g drift h

/-- The bounds use the actual input cursor, the original normalized program
and its acquired packed-profile header. -/
theorem normalized_stage_price (addr head ratio driftR : ℕ)
    (allDates : EveryStage G board op t f g resetCost cut ratio drift driftR bound (quota t) τ B h)
    (address : ProfiledRate.Covers G board op t f g resetCost τ drift bound B h addr)
    (seed : (v).Ready G board op t f g drift h w head)
    (chosen : reset.board=board) (cap : degree ≤ bound) (capacity : drift+1 ≤ scale J driftR)
    (low : 2^h ≤ copies) (high : copies ≤ (2^h)^2)
    (words : (t+1+max addr head+2)*h ≤ w) (bill : w ≤ ratio*h) :
    (∑i∈Finset.range (S).length,(instruction (w:=w) traces menu initial i).tariff)*2^J ≤
      2*(copies*((S).copies*p)) :=by
  have funds : StageLedger X G board op t f g resetCost cut ratio drift driftR bound (quota t) τ B h copies p w lo header degree ordinary reset branch positive room shorten fit :=
    allDates X copies p w lo header degree ordinary reset chosen branch positive room shorten fit
  have fences := DescentDatedSeedStartup.SeedHeader.Input.profile_fences G op t f g drift h v
  exact funds initial capacity cap rfl seed.geometry addr head address seed.head words (S).copies H
    ((v).base G h) ((S).censusBits p) wire hist rfl bill low high fences.1 fences.2

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
