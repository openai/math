import OAI.Hierarchy.TaggedWideNativeMenu
import OAI.Hierarchy.TaggedWidePurchasedFamily

namespace OAI
/-! # Choosing and mounting the physical wide-family format before the parent data -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ReportSockets Tagged TaggedShorterBudget TaggedWidthProfile Filter
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ)

theorem stage_positive : 0<v.W := by have wide:=v.geometry.wide;omega
theorem radius_positive : 0<v.radius := by have high:=v.geometry.large;omega

local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

/-- The program source is uniform in the true physical count certificate and
in high parents. The comparison tolerance and the near and far compactor
instances are all chosen before any tagged inputs or private selectors. -/
def Compiler {κ A ε δ η ξ : ℝ} (u : ℝ→ℝ) (_price : Choice u A ε p q Q σ Λ δ η ξ) : Prop :=
  ∀m:ℕ,v.PhysicalCounts u A δ ξ m→∃ell:ℕ,∀short C,0≤C→
    (∀ᶠ x in WideParent.large κ A, GroupRoom v.W k jobs u δ ξ
      ((typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ) x)→
    HardwareAt (F:=F) (k:=k) (M:=v.radius) (κ:=κ) (A:=A) (u:=u) (δ:=δ) (ξ:=ξ)
      (n:=m) (attempts:=jobs) (ell:=ell) v.stage_positive short C

theorem native_readout {s κ A ε δ η ξ : ℝ} {u : ℝ→ℝ} (hu : Admissible s u) (hk : 0≤κ)
    (price : Choice u A ε p q Q σ Λ δ η ξ) (program : v.Compiler (κ:=κ) u price) :
    Nonempty (ProtocolReadout F k u κ A δ ξ) := by
  obtain ⟨m,density⟩:=v.printed_menu price
  obtain ⟨ell,assembled⟩:=program m density
  exact purchased_readout (F:=F) (n:=m) (attempts:=jobs) (ell:=ell) v.stage_positive hu price hk
    v.radius_positive assembled

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
