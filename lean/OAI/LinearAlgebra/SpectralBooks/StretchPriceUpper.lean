import OAI.LinearAlgebra.SpectralBooks.PermutationControl
import OAI.LinearAlgebra.SpectralBooks.StretchPrice

/-! # Upper price bounds for the same tagged product word

In the first collapsed placement the tag and every controlled permutation are
at a single site. In the second, one grouped linear map supplies an entire
fiber of tags, so the ordinary-sum cost is controlled by the number of words
rather than the number of permutations.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

section

open PermutationControl

variable {K : Type*} [CommSemiring K] {B C : Type} [Fintype B] [Fintype C]

/-- Monotonicity under a linear map on the single site obtained by grouping
`u` with all the sites of `C`. The other sites keep their original coordinates. -/
def SitePriceEval.MonoGroupedC (p : SitePriceEval K B C) : Prop :=
  ∀ {U V : Type} {X : B → Type} {Y Y' : C → Type}
    [Fintype U] [Fintype V] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)] [∀ c, Fintype (Y' c)]
    (T : Tensor K U (∀ i, X i) (∀ i, Y i))
    (A : ((U × (∀ i, Y i)) → K) →ₗ[K] ((V × (∀ i, Y' i)) → K)),
    p.value (fun v x y => A (fun t => T t.1 x t.2) (v, y)) ≤ p.value T

/-- Monotonicity under a linear map on the single site obtained by grouping
`u` with all the sites of `B`. -/
def SitePriceEval.MonoGroupedB (p : SitePriceEval K B C) : Prop :=
  ∀ {U V : Type} {X X' : B → Type} {Y : C → Type}
    [Fintype U] [Fintype V] [∀ b, Fintype (X b)] [∀ b, Fintype (X' b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ i, X i) (∀ i, Y i))
    (A : ((U × (∀ i, X i)) → K) →ₗ[K] ((V × (∀ i, X' i)) → K)),
    p.value (fun v x y => A (fun t => T t.1 t.2 y) (v, x)) ≤ p.value T

/-- Product additivity and the price of the diagonal on `u,C` give this bound
for a product with a finite common label. -/
def SitePriceEval.DiagonalControlBound (p : SitePriceEval K B C) (E : ℝ) : Prop :=
  ∀ {Tag U : Type} {X : B → Type} {Y : C → Type}
    [Fintype Tag] [Nonempty Tag] [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (T : Tensor K U (∀ i, X i) (∀ i, Y i)),
    p.value (diagonalControl (Tag := Tag) T) ≤ p.value T + E * Real.logb 2 (Fintype.card Tag)

variable {U J L Tag : Type} {X : B → Type} {Y : C → Type}
  [Fintype U] [Fintype J] [DecidableEq J] [Fintype Tag] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

/-- Equation `doubling-control-a`. -/
theorem taggedWord_price_upper_a (a : SitePriceEval K B C) {E : ℝ}
    (hdiag : a.DiagonalControlBound E) [Nonempty Tag]
    (T : L → Tensor K U (∀ i, X i) (∀ i, Y i)) (s : J → L) (perm : Tag → Equiv.Perm J) :
    a.value (tagged (fun t y i => y i ∘ perm t) (wordProduct T s)) ≤
      a.value (wordProduct T s) + E * Real.logb 2 (Fintype.card Tag) := by
  exact (a.mono (tagged_siteRestriction_diagonal (wordProduct T s)
    (fun t _ y => y ∘ perm t))).trans (hdiag (Tag := Tag) _)

/-- Equation `doubling-control-bc`. The slice inequality is used only at the
tagged tensor. Reordered words with an empty fiber give the zero map, so the
same estimate also holds for those summands over arbitrary characteristic. -/
theorem taggedWord_price_upper_bc (a b c : SitePriceEval K B C) {E : ℝ}
    (hb : b.MonoGroupedC) (hc : c.MonoGroupedB) (hcSum : c.OrdinarySumBound E)
    [Fintype L] [Nonempty L] (T : L → Tensor K U (∀ i, X i) (∀ i, Y i)) (s : J → L)
    (perm : Tag → Equiv.Perm J)
    (hslice : let Z := tagged (fun t y i => y i ∘ perm t) (wordProduct T s)
      a.value Z ≤ b.value Z + c.value Z) :
    a.value (tagged (fun t y i => y i ∘ perm t) (wordProduct T s)) ≤
      b.value (wordProduct T s) + c.value (wordProduct T s) +
        E * (Fintype.card J : ℝ) * Real.logb 2 (Fintype.card L) := by
  classical
  let Z := tagged (fun t y i => y i ∘ perm t) (wordProduct T s)
  change a.value Z ≤ _ at hslice ⊢
  have hB : b.value Z ≤ b.value (wordProduct T s) :=
    hb (wordProduct T s) (groupedCMap (fun t y i => y i ∘ perm t))
  let G (q : J → L) (S : Tensor K (J → U) (∀ i, J → X i) (∀ i, J → Y i)) :
      Tensor K (Tag × (J → U)) (∀ i, J → X i) (∀ i, J → Y i) := fun u x y =>
    groupedBMap perm s q (fun v => S v.1 v.2 y) (u, x)
  let parts (q : J → L) := G q (wordProduct T q)
  have he : Z = fun u x y => ∑ q, parts q u x y :=
    funext fun u => funext fun x => funext fun y =>
      tagged_wordProduct_eq_groupedB_sum T s perm u x y
  obtain ⟨q, hq⟩ := hcSum parts
  rw [← he] at hq
  have hpart : c.value (parts q) ≤ c.value (wordProduct T s) := by
    by_cases hit : ∃ t, s ∘ (perm t).symm = q
    · obtain ⟨t, rfl⟩ := hit
      exact (hc _ (groupedBMap perm s _)).trans (c.mono (wordProduct_reorder_restriction T s _))
    · have hzero : parts q = G q (wordProduct T s) := by
        funext u x y
        have h : s ∘ (perm u.1).symm ≠ q := fun h => hit ⟨u.1, h⟩
        simp [parts, G, groupedBMap, h]
      rw [hzero]
      exact hc _ (groupedBMap perm s _)
  have hcard : Real.logb 2 (Fintype.card (J → L)) =
      (Fintype.card J : ℝ) * Real.logb 2 (Fintype.card L) := by
    simp [Real.logb_pow]
  rw [hcard] at hq
  calc
    a.value Z ≤ b.value Z + c.value Z := hslice
    _ ≤ b.value (wordProduct T s) +
        (c.value (wordProduct T s) + E * ((Fintype.card J : ℝ) * Real.logb 2 (Fintype.card L))) :=
      add_le_add hB (hq.trans (add_le_add_left hpart _))
    _ = _ := by ring

end

end SpectralBooks
end LinearAlgebra
end OAI
