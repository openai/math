import OAI.Hierarchy.TaggedSharedProduct
import OAI.Hierarchy.TaggedSliceData
import OAI.Hierarchy.TaggedWidthSlices

namespace OAI
/-! # Physical payload slicing at a common address length -/

noncomputable section
namespace Hierarchy.Tagged.Slices
open scoped Classical BigOperators
open CatalystSubstitution.SharedProduct

variable {F : Type*} [Field F] {k h w m : ℕ} (v : Fin m → ℕ)
  (total : ∑ i, v i = w)

include total in
/-- The joined approximation exposes every original data bit. Its gap loses
at most two flat dimensions per slice; its size never exceeds the total bill
for the slices, since their catalyst ports are disjoint. -/
theorem exists_approximation (positive : 0 < m) (X : ∀ i,
    Catalyst.Approximation F k (pins h (v i))) :
    ∃ Y : Catalyst.Approximation F k (pins h w), Y.size ≤ ∑ i, (X i).size ∧
      ∀ G : ℝ, (∀ i, (X i).Gap (coeff F h (v i)) G) →
        Y.Gap (coeff F h w) (G-2*(k:ℝ)*(m:ℝ)) := by
  let : Nonempty (Fin m) := ⟨⟨0,positive⟩⟩
  obtain ⟨Y,size,prices⟩ := exists_product (fun i => pins h (v i)) (pin v total) X
    (fun i => coeff F h (v i))
  refine ⟨Y,?_,fun G hg => ?_⟩
  · have shared := pins_le_sum (h:=h) v total positive
    omega
  · have eq := funext (coefficient (F:=F) v total (h:=h))
    simpa only [eq,Fintype.card_fin] using prices G hg

/-- Split any positive payload at a positive capacity into balanced integer
widths, using the minimum number of such slices. -/
theorem balanced {w C : ℕ} (hw : 0 < w) (hC : 0 < C)
    (X : ∀ i, Catalyst.Approximation F k (pins h (TaggedWidthSlices.width w C i))) :
    ∃ Y : Catalyst.Approximation F k (pins h w), Y.size ≤ ∑ i, (X i).size ∧
      ∀ G : ℝ, (∀ i, (X i).Gap (coeff F h (TaggedWidthSlices.width w C i)) G) →
        Y.Gap (coeff F h w) (G-2*(k:ℝ)*(TaggedWidthSlices.count w C)) :=
  exists_approximation _ (TaggedWidthSlices.sum_width hC) (TaggedWidthSlices.count_pos hw hC) X

end Hierarchy.Tagged.Slices

end
end OAI
