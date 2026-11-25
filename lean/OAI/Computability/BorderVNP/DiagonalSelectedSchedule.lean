import OAI.Computability.BorderVNP.DiagonalPhysicalSchedule
import OAI.Computability.BorderVNP.PackedSelectedHistoryWork

/-! # Concrete source receipt frames inside the simultaneous stretch schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Crossing PackedHistoryCircuit.Normalized Packing TeamScales Epoch Cover
open PackedHistoryCircuit.Normalized.SelectedSchedule
open scoped Classical

universe u v w

variable {D m : ℕ} [NeZero D] {F : Type u} [Field F] {e : PaidIdentity F D m}

/-- The actual public word and row families at every chosen history level,
their verified node evaluations and the total number of gates and guess pins. -/
def selectedReceiptAt (S : SiteSchedule e) {a extra : ℕ} (s : EpochScales S a extra)
    (C p n r : ℕ) : Prop :=
  let T := epochs s.τ n
  let start := CoverScale.initialDepth (Cube D) r n
  let width := 60*logWidth r n
  ∀ (P : Fin T → Type) (bits : ∀ t, P t → ℕ),
    ∃ nodes : ∀ t : Fin T, Nodes S start t width,
      (∀ (t : Fin T) (i : Fin S.rounds),
        let high := S.high (EnrichedOuter.offset S start t)
        SourceTemplate.NodeRun.{u,v} (P := Shortening.Adaptive.Port S.fanIn (P t) i.val)
          (bits := Shortening.Adaptive.width (bits t) S.fanIn i.val)
          (S.source.pattern i) (S.source.stepDepth S.last high i) S.positiveFanIn (S.source.catalog (i.val+1))
          ((2*n*r)^2) (nodes t i)) ∧
      (∀ t i, kernelWork S (nodes t) i ≤ PackedHistoryCircuit.rowWork C (CoverScale.sites (Cube D) start)
        (logWidth r n) p ((before S start t i).parallel S.fanIn)) ∧
      (treeWork S.fanIn S.rounds T (fun t i => kernelWork S (nodes t) i):ℝ) < r*(n:ℝ)^(915/1000:ℝ)

/-- Choose the entire schedule after accounting for the proved cost of the
physical receipt frames. At each length the same batch supports those frames,
the exact private signed cell driver and the rounded parse and epoch offsets. -/
theorem exists_selected_physical_schedule (K : Type*) [Field K] (e : PaidIdentity F D m)
    (hm : 0 < m) (minimum : ℕ) :
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule e, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{v} z) ∧
    ∀ extra : ℕ, ∃ s : EpochScales S (cube.pred+1) extra, ∃ C p : ℕ,
    ∀ E d Q A T B j H R k : ℕ, ∀ limit : ℝ, 0 < limit →
    ∃ b : JointSchedule.{w} s (E+1) (max d p) Q A B j, b.ω ≤ limit ∧
      AdmissibleRange b.ω (selectedReceiptAt.{u,v} S s C p) ∧
      AdmissibleRange b.ω (PrivateCellBudgetAt A T B j H R k) ∧
      ∀ cut : ℕ, ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
        LengthBudget b cut n ∧ selectedReceiptAt.{u,v} S s C p n r ∧ PrivateCellBudgetAt A T B j H R k n r := by
  obtain ⟨cube,hc,S,run,chooseScales⟩ := exists_physical_schedule.{w,v} K e hm minimum
  refine ⟨cube,hc,S,run,?_⟩
  intro extra
  obtain ⟨s,chooseBatch⟩ := chooseScales extra
  obtain ⟨C,p,v,hv,frames⟩ := eventually_selected_receipt_work.{u,v} S hm s
  have charged : AdmissibleRange v (selectedReceiptAt.{u,v} S s C p) := frames
  refine ⟨s,C,p,?_⟩
  intro E d Q A T B j H R k limit hlimit
  obtain ⟨b,cap,cell,sizes⟩ := chooseBatch E (max d p) Q A T B j H R k (min limit v) (lt_min hlimit hv)
  have nodes := charged.shrink (cap.trans (min_le_right ..))
  refine ⟨b,cap.trans (min_le_left ..),nodes,cell,?_⟩
  intro cut
  filter_upwards [sizes cut,nodes.stretched b.rho_omega.le] with n physical receipt
  exact ⟨physical.1,receipt,physical.2⟩

end Diagonal

end BorderVNP
end Computability
end OAI
