import OAI.Hierarchy.TaggedWideControl
import OAI.Hierarchy.TaggedWidthSlices

namespace OAI
/-! # The integer menu of shorter tagged formats -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst Filter
open scoped Topology

/-- One physical format, before splitting the payload at the induction ceiling. -/
structure ShorterBank where
  height : ℕ
  payload : ℕ
  copies : ℕ
  capacity : ℕ

namespace ShorterBank

def slices (b : ShorterBank) := TaggedWidthSlices.count b.payload b.capacity
def width (b : ShorterBank) (j : Fin b.slices) := TaggedWidthSlices.width b.payload b.capacity j

abbrev Output (b : ShorterBank) (F : Type*) (k : ℕ) :=
  Approximation F k (b.copies * pins b.height b.payload)

end ShorterBank

/-- Integer geometry and paid slot counts of one cofinal protocol on a fixed wide
interval. The two limits use the same filter over all parent payloads. -/
structure WideMenu (κ A : ℝ) where
  types : ℕ
  height : Fin types → WideParent κ A → ℕ
  payload : Fin types → WideParent κ A → ℕ
  copies : Fin types → WideParent κ A → ℕ
  T : Fin types → ℝ
  Y : Fin types → ℝ
  ratios : ∀ i, 0 < T i ∧ T i ≤ 1/2 ∧ 0 < Y i
  tall : ∀ i,Tendsto (fun x => (height i x:ℝ)) (WideParent.large κ A) atTop
  heightRatio : ∀ i,Tendsto (fun x => (height i x:ℝ)/x.h) (WideParent.large κ A) (𝓝 (T i))
  widthRatio : ∀ i,Tendsto (fun x => (payload i x:ℝ)/x.w) (WideParent.large κ A) (𝓝 (Y i))

def WideMenu.bank {κ A : ℝ} (m : WideMenu κ A) (x : WideParent κ A) (i : Fin m.types) :
    ShorterBank := ⟨m.height i x,m.payload i x,m.copies i x,⌊(m.height i x:ℝ)^A⌋₊⟩

end Hierarchy.Tagged

end
end OAI
