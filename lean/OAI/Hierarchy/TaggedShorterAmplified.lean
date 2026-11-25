import OAI.Hierarchy.TaggedAmplified
import OAI.Hierarchy.TaggedGapScale

namespace OAI
/-! # The price of an installed shorter-address bank at its parent height -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst Filter CorrectionFrame

/-- The returned constant prices physical size for every dimension and
format. Thresholds are uniform over batch sizes, payload widths and input
circuits. The lower bound on occupied and idle slots is the source of the
parent-scale gain. -/
theorem shorter_batches (F : Type*) [Field F] :
    ∃ K : ℕ, ∀ (k : ℕ) {C fraction b G : ℝ},
      6 ≤ C → 0 < fraction → 0 < b → 0 ≤ G →
      ∃ h₀ t₀ : ℕ, ∀ h t s w : ℕ, h₀≤h → t₀≤t → 3*t≤2*h → 0<s →
      fraction*(2:ℝ)^h ≤ (s:ℝ)*2^t → Real.logb 2 s ≤ (t:ℝ)^b →
      ∀ X : Approximation F k (pins t w), X.Gap (coeff F t w) (gap C t) →
      ∃ Y : Approximation F k (s*pins t w), Y.width = copiesWidth s X.width ∧
        Y.size ≤ K*s*X.size ∧ Y.Gap (dataProduct s (coeff F t w)) (G*gap C h) := by
  obtain ⟨K,power⟩ := amplified_batches F
  refine ⟨K,fun k {C fraction b G} hC fraction_pos bpos Gpos => ?_⟩
  obtain ⟨h₀,global⟩ := eventually_atTop.1
    (GapScale.eventual_shorter_amplification hC fraction_pos (C:=1) zero_le_one Gpos)
  obtain ⟨t₀,perChild⟩ := eventually_atTop.1 ((power b bpos).and
    (GapScale.eventual_interface_threshold C k (C:=1) zero_le_one))
  refine ⟨h₀,t₀,fun h t s w hbig tbig short spos slots logsize X good => ?_⟩
  let H := (((t+1)^2:ℕ):ℝ)
  have eq : H = ((t:ℝ)+1)^2 := by simp [H]
  have fit : H ≤ 1*((t:ℝ)+1)^2 := by simp [eq]
  have pos : 0 < H := by rw [eq]; positivity
  obtain ⟨build,pay⟩ := perChild t tbig
  obtain ⟨Y,shape,size,price⟩ := build X spos logsize good (pay H pos.le fit)
  exact ⟨Y,shape,size,Approximation.Gap.mono _ price
    (global h hbig t s H short slots pos fit)⟩

end Hierarchy.Tagged

end
end OAI
