import OAI.LinearAlgebra.SpectralBooks.GroupedProduct
import OAI.LinearAlgebra.SpectralBooks.StretchProducts
import OAI.LinearAlgebra.SpectralBooks.StretchPriceUpper

/-! # The sum of prices at the two collapsed placements

The product restriction gives an upper bound by the sum of prices of two
private tensors. In each collapsed placement the corresponding private tensor
is obtained by relabeling the coordinates at the common site.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation PermutationStretch
open scoped Classical

variable {K : Type*} [Field K] {B C U : Type} [Fintype B] [Fintype C] [Fintype U]
  {X : B → Type} {Y : C → Type} [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]

/-- Moving the `C` coordinates to the common site costs nothing for a
placement allowing grouped operations on `C`. -/
theorem SitePriceEval.MonoGroupedC.groupRight_le {p : SitePriceEval K B C}
    (hp : p.MonoGroupedC) (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    p.value (groupRight T) ≤ p.value T :=
  hp T (LinearMap.funLeft K K (Prod.fst : (U × (∀ c, Y c)) × (C → Unit) → U × (∀ c, Y c)))

/-- Moving the `B` coordinates to the common site in the second placement. -/
theorem SitePriceEval.MonoGroupedB.groupLeft_le {p : SitePriceEval K B C}
    (hp : p.MonoGroupedB) (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    p.value (groupLeft T) ≤ p.value T :=
  hp T (LinearMap.funLeft K K (Prod.fst : (U × (∀ b, X b)) × (B → Unit) → U × (∀ b, X b)))

/-- The collapsed-placement inequality `doubling-slices`. Private agreement
is only needed at the two private tensors obtained from `T`. -/
theorem collapsed_slice_price_le (a b c : SitePriceEval K B C)
    (ha : a.BinaryProductAdditive) (hb : b.MonoGroupedC) (hc : c.MonoGroupedB)
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) (hT : T ≠ 0)
    (hagB : a.value (groupRight T) = b.value (groupRight T))
    (hagC : a.value (groupLeft T) = c.value (groupLeft T)) :
    a.value T ≤ b.value T + c.value T := by
  let P (p : U × (∀ c, Y c)) (x : ∀ b, X b) := T p.1 x p.2
  let Q (p : U × (∀ b, X b)) (y : ∀ c, Y c) := T p.1 p.2 y
  have hP : P ≠ 0 := fun h => hT (funext fun u => funext fun x => funext fun y =>
    congrFun (congrFun h (u, y)) x)
  have hQ : Q ≠ 0 := fun h => hT (funext fun u => funext fun x => funext fun y =>
    congrFun (congrFun h (u, x)) y)
  calc
    a.value T ≤ a.value (joinedPrivate P Q) := a.mono (siteRestriction_grouped_product T)
    _ = a.value (groupRight T) + a.value (groupLeft T) := value_joinedPrivate a ha P Q hP hQ
    _ = b.value (groupRight T) + c.value (groupLeft T) := by rw [hagB, hagC]
    _ ≤ b.value T + c.value T := add_le_add (hb.groupRight_le T) (hc.groupLeft_le T)

end SpectralBooks
end LinearAlgebra
end OAI
