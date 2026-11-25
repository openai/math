import OAI.Hierarchy.DescentNamedBranchPins
import OAI.Hierarchy.DescentPathParticles
import OAI.Hierarchy.DescentTerminalSiteTokens

namespace OAI
/-! # Uniform local occurrence count of each real terminal coefficient branch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
attribute [local irreducible] Origin.source Origin.archivePackage
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)

theorem Branch.site_particles : (Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).Particles b.target :=
  b.path.particles p hp b.origin.archive b.recorded
    b.origin.particles

/-- Holds uniformly at the actual last shop of every profile, including the exterior hubs.
The geometric exponent depends only on the ordinary schedule and its price exponent. -/
theorem Branch.site_nodes (hh : 0<S.height) (v : ((Epochs.finish G hu he r).state c).graph.Site) :
    Fintype.card ((Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit.recipe v).Node ≤ S.epochPower^S.localTokenExponent := by
  have real := Branch.site_particles X G S b hp
  apply (Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp).bit.local_nodes b.target.placement S real.nodes hh b.target.valid.atom (Nat.le_refl _)
    (b.target.grain.trans (S.grain_terminal G.b p).symm) b.target.atoms b.target.edges b.target.valid.capacity
    real.attached _ real.balance v
  intro pin
  simpa using b.target.atoms.symm

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
