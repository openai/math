import OAI.Hierarchy.TaggedRadixFormats
import OAI.Hierarchy.TaggedRadixFeasible

namespace OAI
/-! # Installing the schedule of padded, stable low-to-high digit passes -/
namespace Hierarchy.Tagged.Radix
open Filter
variable {F : Type*} [Field F] {k : ℕ} {a B : ℝ}

theorem layout_of_start_runs (ha : 1<a) (hB : 1<B) (shell : ℕ)
    (runs : ∀ᶠ h : ℕ in atTop, ∀ n, n+1=passesFor a h → h+1≤(n+1)*digitBits a h →
      ∀ Y : ∀ i,(passFormatAt a B h n i (2*h+4)).Calls F k,
        ∃ S : StageRun h n Y,S.Room shell) : Layout F k a B := by
  refine ⟨2,6,8,shell,6,by decide,by norm_num,?_⟩
  filter_upwards [eventual_start_formats ha hB,runs] with h bound run
  obtain ⟨n,eq,enough,price,formats⟩ := bound
  exact ⟨n,fun i => passFormatAt a B h n i (2*h+4),price,formats,run n eq enough⟩

end Hierarchy.Tagged.Radix

end OAI
