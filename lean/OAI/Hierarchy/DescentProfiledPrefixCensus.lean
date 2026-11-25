import OAI.Hierarchy.DescentNamedBranchMachine
import OAI.Hierarchy.DescentSnapshotCutGrain
import OAI.Hierarchy.DescentPackedCensusInvoice

namespace OAI
/-! # Precision of the funded count at every actual cut of the normalized trace -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => issued X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)


set_option hygiene true
variable (walk : (last).Choice)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}

attribute [local irreducible] issued

theorem profiled_prefix_census (height : 0<S.height) (before : Path (trace walk).origin.source r)
    (after_ : Path r (trace walk).target) (joined : before.append after_=(trace walk).path) :
    r.placement.wire*(r.placement.z*G.b)*r.placement.cap<2^(S.censusBits p) :=by
  have age : i + after_.kinds.length = S.length := after_.kinds_length
  have dated : i ≤ S.length := age ▸ Nat.le_add_right i after_.kinds.length
  let t := traceAt X G S ordinary reset branch positive room shorten walk
  have tk : t.path.kinds = kindCalendar S.rounds S.height := by
    dsimp only [t, traceAt]
    exact (trace walk).kinds
  have tf : t.firstGrain = S.grainAt G.b p 0 := by
    dsimp only [t, traceAt]
  let atFirst : Path t.first r := by
    dsimp only [t, traceAt]
    exact before
  let atLast : Path r t.last := by
    dsimp only [t, traceAt]
    exact after_
  have atTrace : atFirst.append atLast = t.path := by
    dsimp only [t, traceAt, atFirst, atLast]
    exact joined
  have grain : z = S.grainAt G.b p i := Path.snapshot_cut_grain
    (t:=t) (r:=r) (p:=p) tk tf atFirst atLast atTrace
  exact (r.placement.census_caps_at S r.valid height dated (r.grain.trans grain) r.edges branch).2

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
