import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentTerminalCandidateHistory
import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentTerminalSeedCircuit
import OAI.Hierarchy.DescentWideFullPinInvoice

namespace OAI
/-! # The original marked seed circuit on the normalized chart's actual candidate pins -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice DescentExterior Catalyst
open ThreeFlat Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
variable (w : ℕ) (fit : S.firstWidth G.b (W*piece) < 2^w) {j rest K : ℕ} (cfg : DescentTerminalCompiledPrefix.Shape)
local notation "s" => S.firstWidth G.b (W*piece)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local instance : Fintype (ch).Pin := (ch).finite
local notation "E" => Fintype.card (Port P X.width)
local notation "Old" => (ch).Pin ⊕ Hidden E j rest s
local notation "All" => DescentTerminalFullPins.Candidate Old K W q piece cfg.terminal.plane.rawRows
local notation "liftSeed" => DescentTerminalFullPins.history (old:=Old) ∘ Sum.inl ∘ (ch).seed

/-- The radix chip reads exactly the original seed pins through the two candidate injections. -/
def wideChoiceCircuit : BitNetwork F (Fintype.card All) :=
  DescentTerminalSeedChip.circuit X (liftSeed : _ → All)

local notation "chip" => wideChoiceCircuit (K:=K) (W:=W) (q:=q) (piece:=piece) X G S ordinary reset branch positive room shorten w fit (j:=j) (rest:=rest) cfg

theorem wideChoiceCircuit_size : (chip).cells+(chip).internal =
    Fintype.card (DescentSeedRoot.CountKey X S.copies)*DescentSeedRoot.digitsNeeded s :=
  DescentTerminalSeedChip.size X (liftSeed : _ → All)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
