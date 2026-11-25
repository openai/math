import OAI.Hierarchy.DescentNamedOperandBill
import OAI.Hierarchy.DescentOriginalRangeSlots
import OAI.Hierarchy.DescentBundleNodeCapacity
import OAI.Hierarchy.DescentResetRetainedCalendarWidths

namespace OAI
/-! # Flattened argument capacity at every cut of the named trajectory -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentKernelHistory DescentResetInvoice Catalyst Chronology
open DescentBundleHistory
open scoped Classical BigOperators
noncomputable section
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

section
variable {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
variable {U : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width)))
    (fun _ => S.firstWidth G.b p * 1)} {i z' D : ℕ}
    {cur : Reached U G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z' D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (before : Path b.origin.source cur) (whole : before.whole p)

theorem Branch.prefix_argument_capacity (hh : 0<S.height) (base : G.b≤2^S.capGain)
    (shape : WorldShape p R (before.archive p hp b.origin.archive whole).bit)
    (v : U.graph.Site) (n : ((before.archive p hp b.origin.archive whole).bit.recipe v).Node) :
    (DescentRetainedRangeDigits.occurrences (shape.sites v) n).length≤S.retainedArgumentsAt G R :=by
  rw [DescentRetainedRangeDigits.length _ _ hp]
  exact (shape.sites v).node_keys_le hp n R _ (shape.stride v n)
    (Branch.prefix_node_bits X G S b hp before whole hh base v n)

end
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
