import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentDatedBranchEvents

namespace OAI
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

/-- Real endpoints of the normalized named history of this particular ballot. -/
def traceAt (c : (last).Choice) : RunTrace G q epsilon S k price s S.length
    (fun _ : (Σ _ : Fin S.copies, Fin (Fintype.card (Port nP X.width)))=>s*1) 0 :=
  ⟨_,_,_,_,_,_,(actual c).origin.source,(actual c).target,(actual c).path⟩

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten

attribute [local irreducible] issued

private theorem traceAt_kinds (c : (last).Choice) :
    (traces c).path.kinds = kindCalendar S.rounds S.height := by
  dsimp only [traceAt]
  exact (actual c).kinds

/-- The same date cannot be ordinary on one named branch and a reset on another. -/
theorem event_kind (i : ℕ) (a b : (last).Choice)
    (left : (traces a).path.Event i) (right : (traces b).path.Event i) :
    left.isReset=right.isReset :=by
  apply left.compatible right
  exact (traceAt_kinds X G S ordinary reset branch positive room shorten a).trans
    (traceAt_kinds X G S ordinary reset branch positive room shorten b).symm

/-- Compile the original candidate's real local date on a common static calendar.
Only comparisons of two ordinary sites or two resets enter the code equality. -/
theorem shared_instruction {w : ℕ} (code : ∀i,RunTrace.Events traces i→DateCode w)
    (ordinaryCode : ∀i,∀x y : RunTrace.Events traces i,
      x.2.isReset=false→y.2.isReset=false→code i x=code i y)
    (resetCode : ∀i,∀x y : RunTrace.Events traces i,
      x.2.isReset=true→y.2.isReset=true→code i x=code i y)
    (i : ℕ) (c : (last).Choice) (e : (traces c).path.Event i) :
    RunTrace.machine traces code i=code i ⟨c,e⟩ :=by
  apply RunTrace.on_branch
  intro j x y
  have same:=event_kind X G S ordinary reset branch positive room shorten j x.1 y.1 x.2 y.2
  cases hx:x.2.isReset with
  | false=>exact ordinaryCode j x y hx (same.symm.trans hx)
  | true=>exact resetCode j x y hx (same.symm.trans hx)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
