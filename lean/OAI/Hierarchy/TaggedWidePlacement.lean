import OAI.Hierarchy.TaggedWideHistoryUnit
import OAI.Hierarchy.TaggedWideAddressShape
import OAI.Hierarchy.ProbeFixedOriginalSockets
import OAI.Hierarchy.ProbeFixedLinkMenu

namespace OAI
/-! # Selecting the same concrete published and private placement for each native program -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def wideJoint (h width : ℕ) := WideMemory.joint v.sampler h v.W k v.wideJobs v.depth
  v.mesh.reserveSteps v.keepLimit width v.precision

def wideSources (h width : ℕ) := v.sourcePair h width (WideMemory.K h v.W)
  (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
  (WideMemory.R v.sampler h v.W k) (CoreCatalogue.pointBits h v.W) 0 (v.wideJoint h width)

def widePlacement (h width : ℕ) : v.Placement :=
  let sources:=v.wideSources h width
  v.catalystPlacement h (WideMemory.K h v.W) (WideMemory.dir h v.W k v.wideJobs).groups
    (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
    (v.wideJoint h width) sources.1 sources.2

def wideOrder (h width : ℕ) : Fin (v.widePlacement h width).catalogue.coreRows ≃ Edges v.sampler h (2^v.W) k :=
  WideMemory.order v.sampler h v.W k

theorem wideCatalogueRows (h width : ℕ) :
    (v.widePlacement h width).catalogue.rows≤v.rowFactor*2^h :=
  v.board_rows _ (v.wideOrder h width) rfl

theorem wideGeometryPrefix (h width : ℕ) :
    let P:=v.widePlacement h width
    2^h≤P.joint.initial ∧ Native.heapEnd h (2^v.W) Native.copies≤P.joint.initial ∧
      CoreRoute.stop v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
        (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
        (WideMemory.R v.sampler h v.W k)≤P.joint.initial := WideMemory.ordered ..

theorem wideGeometryHeight :
    ∃c:ℕ,∀ h width,(v.widePlacement h width).joint.initial≤c*2^h := by
  obtain ⟨c,paid⟩:=WideMemory.first_linear v.sampler v.W k v.wideJobs v.depth
  exact ⟨c,fun h _=>paid h⟩

theorem wideJointHeight :
    ∃c:ℕ,∀ h width,v.keepLimit*width+1≤2^h →
      JointHeader.stop (v.widePlacement h width).joint h (publicStages v.W) k
        (DeadlineROM.count v.mesh)≤c*2^h := by
  obtain ⟨c,bound⟩:=WideMemory.joint_linear v.sampler v.W k v.wideJobs v.depth (publicStages v.W)
    v.mesh.reserveSteps (DeadlineROM.count v.mesh)
  exact ⟨c,fun h width fit=>bound h v.keepLimit width v.precision fit⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
