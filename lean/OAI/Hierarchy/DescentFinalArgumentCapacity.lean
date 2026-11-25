import OAI.Hierarchy.DescentPrefixArgumentCapacity
import OAI.Hierarchy.DescentNamedHistoryShape

namespace OAI
/-! # Original operand capacity at the last node of a named branch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentKernelHistory DescentResetInvoice Catalyst Chronology
open DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F]
variable {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "archive" => Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp

/-- Apply the recorded prefix bound to the entire branch, retaining the actual argument order. -/
theorem Branch.final_argument_capacity (stride : 1≤R) (hh : 0<S.height) (base : G.b≤2^S.capGain)
    (v : ((Epochs.finish G hu he r).state c).graph.Site) (node : ((archive).bit.recipe v).Node) :
    (((Branch.bundleShape X G S b hp stride).sites v).recipe hp).arity node≤S.retainedArgumentsAt G R :=by
  let shape:=Branch.bundleShape X G S b hp stride
  have full:=b.path.recorded_whole p b.recorded
  have paid:=Branch.prefix_argument_capacity X G S b hp b.path full hh base shape v node
  exact (DescentRetainedRangeDigits.length (shape.sites v) node hp).symm.le.trans paid

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
