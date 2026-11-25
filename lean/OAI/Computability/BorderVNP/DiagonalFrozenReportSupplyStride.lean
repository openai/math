import OAI.Computability.BorderVNP.DiagonalFrozenSignedPostWindows
import OAI.Computability.BorderVNP.DiagonalTallyReportCost
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # The returned source word and real report tail fit a single frozen cell bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open TeamScales DiagonalTallyCellReports Packing
open scoped BigOperators

private theorem groupWeight_le_total {J C : ℕ} (home : Fin J → Fin C) (source : Fin J → ReportBundle) (c : Fin C) :
    weightedCopies ((BundleDirectory.sourceRows home c.val).map source) ≤ ∑ j, (source j).useCount := by
  let f := fun j => (source j).useCount
  have sub : (BundleDirectory.sourceRows home c.val).Sublist (List.finRange J) := List.filter_sublist
  have charge := (sub.map f).sum_le_sum (fun x _ => Nat.zero_le x)
  simpa only [weightedCopies,List.map_map,Function.comp_def,List.finRange,List.map_ofFn,List.sum_ofFn,f] using charge

/-- A single receiving team's source report fits its actual cell stride.
Only the immutable original bundle roster is counted when bounding one
bucket of locally observed multiplicities. -/
theorem Layout.FinishWindows.reportSupplyStride {t : Layout} {r w p d expBits X P L reader n J : ℕ}
    (windows : t.FinishWindows r w p d expBits X P L reader) (hr : 1≤r) (hn : 1≤n)
    (word : t.p.report.countWidth=w) (uses : t.p.report.uses=t.cube.teams*(t.p.parameters*expBits))
    (stride : 3*(r*n)^2+1 ≤ t.cube.cellStride) (source : Fin J → ReportBundle)
    (home : Fin J → Fin t.cube.cells) (expanded : ∑ j,(source j).useCount ≤ t.p.report.uses)
    (m : ℕ → ℕ) (offsets : ℕ) (c : Fin t.cube.cells)
    (supplied : m (offsets+2*t.cube.cables+c.val) ≤ width n (1/5:ℝ)) :
    m (offsets+2*t.cube.cables+c.val) +
      (t.p.report.gadgets*t.p.report.countWidth + weightedCopies ((BundleDirectory.sourceRows home c.val).map source)) ≤ t.cube.cellStride := by
  have small : width n (1/5:ℝ) ≤ n := Nat.floor_le_of_le
    ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 1≤(n:ℝ)) (by norm_num : (1/5:ℝ)≤1)).trans_eq (Real.rpow_one _))
  have dim : t.p.report.gadgets ≤ t.dim+1 := (Nat.le_add_left ..).trans (Nat.le_succ _)
  have rectangle := windows.rectangle
  have counts : t.p.report.gadgets*t.p.report.countWidth ≤ r := by
    rw [word]
    calc
      _ ≤ (t.dim+1)*(w+1) := Nat.mul_le_mul dim (Nat.le_succ _)
      _ ≤ (512*(t.cube.teams+1))*((t.dim+1)*(w+1)) := Nat.le_mul_of_pos_left _ (by positivity)
      _ = 512*(t.cube.teams+1)*(t.dim+1)*(w+1) := by ring
      _ ≤ _ := (Nat.le_add_right ..).trans rectangle
  have bits := (groupWeight_le_total home source c).trans (expanded.trans (uses ▸ windows.slots))
  have square := Nat.le_self_pow (by decide : 2≠0) (r*n)
  have size := (Nat.le_mul_of_pos_left n hr).trans square
  have batches := (Nat.le_mul_of_pos_right r hn).trans square
  omega

end RoutingISA.SignedTaskArena

namespace Diagonal

open Crossing Branch Cover Packing PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open RoutingISA RoutingISA.SignedTaskArena GeometryAdvice TeamScales TeamContraction.ProcessorSlots
open DiagonalTallyCellReports
open scoped BigOperators

variable {F K : Type} [Field F] [Field K] {D M : ℕ} [NeZero D] {G : PaidIdentity F D M}
    {S : SiteSchedule G} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) dlog Q A B j)

/-- The selected arena's width, global occurrence capacity and cell stride
are exactly those used by the emitted local allocation. The threshold data
and original roster suffice for arbitrary receiving memory. -/
theorem JointSchedule.frozenSignedTask_reportSupplyStride (n l size headerFactor : ℕ) (initial : StartupArena)
    (dir : Directory.Layout) (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories) (hn : 1≤n) :
    let r := stretch b.ρ n
    let w := b.physical.word n
    let expBits := Nat.clog 2 (r*(2*l+1)+1)
    let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
    ∀ {p d X P L reader J : ℕ}, task.FinishWindows r w p d expBits X P L reader →
      ∀ (source : Fin J → ReportBundle) (home : Fin J → Fin task.cube.cells),
      (∑ j,(source j).useCount) ≤ task.p.report.uses → ∀ (m : ℕ → ℕ) (offsets : ℕ) (c : Fin task.cube.cells),
      m (offsets+2*task.cube.cables+c.val) ≤ width n (1/5:ℝ) →
      m (offsets+2*task.cube.cables+c.val) +
        (task.p.report.gadgets*task.p.report.countWidth + weightedCopies ((BundleDirectory.sourceRows home c.val).map source)) ≤ task.cube.cellStride := by
  intro r w expBits task p d X P L reader J windows source home expanded
  exact windows.reportSupplyStride (stretch_one b.ρ n) hn rfl rfl le_rfl source home expanded

end Diagonal

end BorderVNP
end Computability
end OAI
