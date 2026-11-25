import OAI.Hierarchy.TaggedWideFormatBounds
import OAI.Hierarchy.TaggedWidthInduction

namespace OAI
/-! # Balanced shorter formats in the domain of the tagged induction -/

namespace Hierarchy.Tagged
open Filter TaggedWidthSlices
open scoped Topology

theorem eventually_wide_formats {ι τ : Type*} [Fintype τ] {l : Filter ι} {κ A : ℝ}
    (hk : 0<κ) (hA : 1<A) (h w : ι→ℕ) (hp wp : τ→ι→ℕ) (T Y : τ→ℝ)
    (types : ∀ k, 0<T k ∧ T k≤1/2 ∧ 0<Y k)
    (large : ∀ k,Tendsto (fun i=>(hp k i:ℝ)) l atTop)
    (height : ∀ k,Tendsto (fun i=>(hp k i:ℝ)/h i) l (𝓝 (T k)))
    (payload : ∀ k,Tendsto (fun i=>(wp k i:ℝ)/w i) l (𝓝 (Y k)))
    (parents : ∀ᶠ i in l, 1<(h i:ℝ) ∧ 0<w i ∧
      Real.logb (h i) (w i)∈Set.Icc (1+κ) A) :
    ∃ B : ℕ, ∀ᶠ i in l, ∀ k,
      let C := ⌊(hp k i:ℝ)^A⌋₊
      3*hp k i≤2*h i ∧ count (wp k i) C≤B ∧
      ∀ j,inRange A (hp k i) (TaggedWidthSlices.width (wp k i) C j) :=
  wide_format_bounds hk hA h w hp wp T Y types large height payload parents

end Hierarchy.Tagged

end OAI
