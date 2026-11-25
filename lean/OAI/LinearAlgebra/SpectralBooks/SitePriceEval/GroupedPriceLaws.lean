import OAI.LinearAlgebra.SpectralBooks.SlicePrice
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Price invariance under grouping and monotonicity of grouped operations

A linear map on grouped coordinates is an ordinary matrix at the common site
after grouping. This identifies the grouping-invariance statement of the
transport estimate with the grouped monotonicity used in permutation stretch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped Classical

namespace SitePriceEval

variable {K : Type*} [Field K] {B C : Type} [Fintype B] [Fintype C]
  (p : SitePriceEval K B C)

/-- The price is invariant under relocating every `C` coordinate to the common site. -/
def GroupingInvariantC : Prop :=
  ∀ {U : Type} {X : B → Type} {Y : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)), p.value (groupRight T) = p.value T

/-- The corresponding invariance under relocation of the `B` coordinates. -/
def GroupingInvariantB : Prop :=
  ∀ {U : Type} {X : B → Type} {Y : C → Type}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)), p.value (groupLeft T) = p.value T

theorem monoGroupedC_iff_groupingInvariant : p.MonoGroupedC ↔ p.GroupingInvariantC := by
  constructor
  · intro hp U X Y _ _ _ T
    apply le_antisymm (hp.groupRight_le T)
    exact hp (groupRight T) (LinearMap.funLeft K K
      (fun t : U × (∀ c, Y c) => (t, fun _ : C => ())))
  · intro hinv U V X Y Y' _ _ _ _ _ T A
    rw [← hinv (fun v x y => A (fun t => T t.1 x t.2) (v, y)), ← hinv T]
    apply p.mono
    apply siteRestriction_central_map _ _ (LinearMap.toMatrix' A)
    intro v x _
    exact congrFun (A.toMatrix'_mulVec (fun t => T t.1 x t.2)) v

theorem monoGroupedB_iff_groupingInvariant : p.MonoGroupedB ↔ p.GroupingInvariantB := by
  constructor
  · intro hp U X Y _ _ _ T
    apply le_antisymm (hp.groupLeft_le T)
    exact hp (groupLeft T) (LinearMap.funLeft K K
      (fun t : U × (∀ b, X b) => (t, fun _ : B => ())))
  · intro hinv U V X X' Y _ _ _ _ _ T A
    rw [← hinv (fun v x y => A (fun t => T t.1 t.2 y) (v, x)), ← hinv T]
    apply p.mono
    apply siteRestriction_central_map _ _ (LinearMap.toMatrix' A)
    intro v _ y
    exact congrFun (A.toMatrix'_mulVec (fun t => T t.1 t.2 y)) v

end SitePriceEval

end SpectralBooks
end LinearAlgebra
end OAI
