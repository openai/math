import OAI.Hierarchy.DescentNormalizedEpochs
import OAI.Hierarchy.DescentPathParticles
import OAI.Hierarchy.DescentTerminalSiteTokens

namespace OAI
/-! # Uniform local occurrence count of each real terminal coefficient branch -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height (initialGroup X S.copies (S.firstWidth G.b p))}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p)

theorem NativeBranch.site_particles : (NativeBranch.archive X G S b hp).Particles b.target :=
  b.path.particles p hp _ b.recorded
    (Chronology.seed_particles X (Chronology.epochsSource G r c) b.source (S.initialDigits radix) b.seed)

/-- Holds uniformly at the actual last shop of every profile, including the exterior hubs.
The geometric exponent depends only on the ordinary schedule and its price exponent. -/
theorem NativeBranch.site_nodes (hh : 0<S.height) (v : ((Epochs.finish G hu he r).state c).graph.Site) :
    Fintype.card ((NativeBranch.archive X G S b hp).bit.recipe v).Node≤S.epochPower^S.localTokenExponent := by
  have real := NativeBranch.site_particles X G S b hp
  apply (NativeBranch.archive X G S b hp).bit.local_nodes b.target.placement S real.nodes hh b.target.valid.atom (Nat.le_refl _)
    (b.target.grain.trans (S.grain_terminal G.b p).symm) b.target.atoms b.target.edges b.target.valid.capacity
    real.attached _ real.balance v
  intro pin
  simpa using b.target.atoms.symm

end
end Hierarchy.DescentSixParty

end OAI
