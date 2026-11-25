import OAI.Hierarchy.DescentNamedLeafBookRoom
import OAI.Hierarchy.DescentTerminalPublicGroup

namespace OAI
/-! # Original terminal site and port order for a reached named epoch -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 500000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))

/-- The original pin permutation retains its physical host. Therefore the stable
whole-word public flight and the per-vertex local port code have the same order. -/
theorem leaf_clustered (retained : j ≤ S.groupWidth k tail S.length+k) :
    DescentTerminalPublicGroup.Clustered net b.target.home (leafExternal X G S b hp base width) := by
  let pins := NativeBranch.rawPin S (X:=X) (radix:=radix) base width
  let rows := chart (j:=j) (r:=rest) (publicLayout X G S b hp base width)
  let owners := publicHost X G S b hp base width
  let home := fun z => b.target.home ((net).attach z)
  have same z : home z = owners (rows (pins.symm z)).1 := by
    have atPin := public_host_read X G S b hp base width retained (pins.symm z)
    simpa only [pins, Equiv.apply_symm_apply, home, owners, rows] using atPin
  intro x y lt
  exact DescentTerminalExteriorPackets.clustered (pins.symm.trans rows) owners home same lt

theorem leaf_home : (leafOrder X G S b hp base width).home = b.target.home := rfl

theorem leaf_ranking (x : (net).Site) :
    (leafOrder X G S b hp base width).nodeRank x =
      (b.target.placement.site b.target.vertex b.target.valid.coordinates x).val := rfl

theorem leaf_arity {q : ℕ} (socketRoom : NativeBranch.localLimit G S ≤ q)
    (i) (v : Fin ((leafOrder X G S b hp base width).site i).nodes) :
    ((leafOrder X G S b hp base width).site i).arity v ≤ q :=
  ((leaf_book_bounds X G S b hp base width i).2.2.1 v).trans socketRoom

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
