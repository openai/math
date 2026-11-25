import OAI.Hierarchy.DescentNamedBranchMachine
import OAI.Hierarchy.DescentChronologicalFinalEvent

namespace OAI
/-! # The reached final reset of the actual issued ballot -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open Computability.VPVNP.BurstRAM PrivateRAM
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
variable (c : (Epochs.finish G _ _ (SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice) (height : 0<S.height)

attribute [local irreducible] issued

/-- Locate the final paid reset in this very ballot. Its predecessor and its
closed reset are available by case analysis on the returned certificate. -/
def issuedFinalReset : Path.FinalReset p (traces c).path := by
  dsimp only [traceAt]
  exact ((actual c).path).finalReset p (actual c).recorded (by
    rw [(actual c).kinds]
    exact kindCalendar_last S.rounds height)

local notation "ticket" => issuedFinalReset X G S ordinary reset branch positive room shorten c height
local notation "age" => S.length-1
variable {w : ℕ} (code : ∀i,RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i→DateCode w)
variable (ordinaryCode : ∀i,∀x y : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i,
      x.2.isReset=false→y.2.isReset=false→code i x=code i y)
    (resetCode : ∀i,∀x y : RunTrace.Events (traceAt X G S ordinary reset branch positive room shorten) i,
      x.2.isReset=true→y.2.isReset=true→code i x=code i y)
local notation "calendar" => RunTrace.machine traces code
local notation "atLast" => code age ⟨c,(ticket).event⟩

include ordinaryCode resetCode in
/-- The fixed program emits the original posted reset instruction at the
last nonempty epoch, on both the incoming and final native store. -/
theorem issued_last_runs (boot : Memory w)
    (total : ∃out,(atLast).Runs (DateCode.history calendar boot age) out) :
    (atLast).Runs (DateCode.history calendar boot age) (DateCode.history calendar boot S.length) :=by
  have same:=shared_instruction X G S ordinary reset branch positive room shorten code ordinaryCode resetCode
    age c (ticket).event
  have runAt:=DateCode.history_step calendar boot age (same.symm ▸ total)
  rw [same,(ticket).succ_age] at runAt
  exact runAt

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
