import OAI.Computability.VPVNP.CompressorShrinkBundleAbsolute
import OAI.Computability.VPVNP.CompressorShrinkBundleFrame
import OAI.Computability.VPVNP.CompressorShrinkBundleWalk

/-!
# The eleven scheduled sources of the dense shrinking setup

The ten setup scans begin at the completed greedy directory. The absolute-ID
scatter starts in their joint post-memory, leaving the typed old directory and
the sorted demand tables available for selection.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkBundlePlan.Scheduled

open BurstRAM Compression PhaseRecipe

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : ShrinkInput.Run X T start m)

local notation "Z" => ShrinkInput.plan X start
local notation "S" => (Fintype.card X.Base * 2^(packingLaneBits a g) : ℕ)
local notation "A" => ShrinkRankSpace.Shape.A (ShrinkInput.plan X start)
local notation "B" => ShrinkRankSpace.Shape.B (ShrinkInput.plan X start)
local notation "Q" => ShrinkRankSpace.Shape.Q (ShrinkInput.plan X start)

private theorem walk_charge {rs : List (Report w)} (abs : AbsoluteRun r rs) :
    RAMBuckets.cost Report.probes (preparationReports X T start r ++ rs) =
      9*S+4*B+(Q+38)*A+4*(B*Q) := by
  have sites := r.siteWork.cost
  have clear := r.ranking.clearCharge
  have rank := r.ranking.ranked.cost
  have widths := r.widths.cost
  change RAMBuckets.cost Report.probes r.sites = 9*S at sites
  change RAMBuckets.cost Report.probes r.clear = 4*B at clear
  change RAMBuckets.cost Report.probes r.classify + RAMBuckets.cost Report.probes r.append +
    RAMBuckets.cost Report.probes r.gather + RAMBuckets.cost Report.probes r.rank = (Q+23)*A at rank
  change RAMBuckets.cost Report.probes r.scatter + RAMBuckets.cost Report.probes r.thickPrefixes +
    RAMBuckets.cost Report.probes r.cdPrefixes + RAMBuckets.cost Report.probes r.abPieces = 10*A+4*(B*Q) at widths
  simp only [preparationReports,RAMBuckets.cost_append]
  have last := abs.charge
  rw [Nat.add_mul] at rank ⊢
  omega

/-- Actual native sources from the first placement read through the last CD
identifier, with the physical state supplied to the demand and term workers. -/
theorem dense_sources (shape : DescriptorSpace.Shape) (step : ℕ) (origin : Expr)
    (room : ShrinkInput.stop X start < 2^w) :
    ∃ rs, SourceWalk (Source X T start shape step origin) order r.greedy.post rs ∧
      let out := after r.greedy.post (eventLog rs)
      ShrinkInput.Retained X T start out ∧
      MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber (absoluteHead Z w) out ∧
      RAMBuckets.cost Report.probes rs = 9*S+4*B+(Q+38)*A+4*(B*Q) ∧
      rs.length = S+2*B+7*A+B*Q ∧
      (∀ j, j < (Z).gathered ∨ (Z).ranks ≤ j → out j = r.post j) ∧
      ∀ next : Memory w, (∀ j < ShrinkInput.stop X start, next j = out j) →
        MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber (absoluteHead Z w) next := by
  have fit : (Z).stop < 2^w := by change (Z).stop+6*(B*Q)+2*B < _ at room; omega
  obtain ⟨rs,abs⟩ := run_absolute r fit
  have head := preparation_sources shape step origin X T start r fit
  have run : Source X T start shape step origin .absolute r.post rs := abs.native
  have tail := SourceWalk.singleton run
  rw [← preparation_post X T start r] at tail
  have full := head.append tail
  refine ⟨_,full,?_⟩
  dsimp only
  rw [SourceWalk.after_append,preparation_post]
  refine ⟨r.keepAbsoluteFrame room abs.frame,abs.directory,walk_charge r abs,?_,abs.frame,fun _ keep ↦ abs.directory_after r keep⟩
  have size := full.report_count (Stage.limit X start) (fun _ _ _ source ↦ source_calls shape step origin X T start source)
  have split := BundleKeys.bundle_rows_total (Fintype.card X.Base) a g
  change B*thickCount a+B*Q = A at split
  change _ = S+(2*B+(A+(A+(A+(A+(A+(B*thickCount a+(B*Q+(B*Q+(A+0)))))))))) at size
  omega

end CompressorRecords.ShrinkBundlePlan.Scheduled

end VPVNP
end Computability
end OAI
