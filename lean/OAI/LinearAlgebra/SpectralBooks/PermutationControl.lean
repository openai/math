import OAI.LinearAlgebra.SpectralBooks.PermutationStretch
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fintype.BigOperators

/-! # The two upper restrictions for permutation stretch

Tensor coordinates are ordered as the common site, the sites of `B`, and the sites
of `C`. A tag selects a permutation of the tensor factors. For the first restriction
each site of `C` reads its own copy of the tag. For the collapsed placements the maps
act on one grouped site. Distinct tags with the same reordered sequence come from a
single copy of that product tensor.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace PermutationControl

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

noncomputable section

variable {K U B C Tag : Type*} [CommSemiring K]

/-- Coefficients of the tagged sum `𝓟(T)`, with the tag in the first slot. -/
def tagged (readC : Tag → C → C) (T : Tensor K U B C) :
    Tensor K (Tag × U) B C :=
  fun x b c => T x.2 b (readC x.1 c)

theorem tagged_sum {J : Type*} [Fintype J] (readC : Tag → C → C)
    (T : J → Tensor K U B C) :
    tagged readC (fun x b c => ∑ j, T j x b c) =
      fun x b c => ∑ j, tagged readC (T j) x b c := rfl

section LocalControl

variable {I : Type*} {V : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Fintype (V i)] [Fintype Tag] [Fintype U] [Fintype B]

/-- Product with a common diagonal label at `u` and at every site of `C`. -/
def diagonalControl (T : Tensor K U B (∀ i, V i)) :
    Tensor K (Tag × U) B (∀ i, Tag × V i) := by
  classical
  exact fun x b c =>
    if ∀ i, (c i).1 = x.1 then T x.2 b (fun i => (c i).2) else 0

/-- Each matrix in the product over `i` acts at one original site of `C`.
Only that site's own diagonal label is read, and the matrix at `u` keeps its tag. -/
private theorem tagged_eq_restrict_diagonal (T : Tensor K U B (∀ i, V i))
    (read : Tag → ∀ i, V i → V i) :
    ∃ (A : (Tag × U) → (Tag × U) → K) (M : B → B → K)
      (P : ∀ i, V i → (Tag × V i) → K),
    tagged (fun t c i => read t i (c i)) T =
      Tensor.restrict A M (fun c d => ∏ i, P i (c i) (d i)) (diagonalControl T) ∧
      ∀ b d, M b d = (by classical exact if d = b then 1 else 0) := by
  classical
  refine ⟨fun x d => if d = x then 1 else 0, fun b d => if d = b then 1 else 0,
    fun i c d => if d.2 = read d.1 i c then 1 else 0, ?_, fun _ _ => rfl⟩
  funext x b c
  symm
  unfold Tensor.restrict
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single b]
    · rw [Finset.sum_eq_single (fun i => (x.1, read x.1 i (c i)))]
      · simp [diagonalControl, tagged]
      · intro d _ hd
        by_cases h : ∀ i, (d i).1 = x.1
        · have hn : ¬ ∀ i, (d i).2 = read (d i).1 i (c i) := by
            intro he
            exact hd (funext fun i => Prod.ext (h i) ((he i).trans (by rw [h i])))
          simp [Fintype.prod_boole, hn]
        · simp [diagonalControl, h]
      · simp
    · intro d _ hd
      simp [hd]
    · simp
  · intro d _ hd
    simp [hd]
  · simp

/-- The first upper restriction in the permutation stretch: the matrices are local
even before collapsing either side of the book. -/
theorem tagged_siteRestriction_diagonal {H : Type*} [Fintype H] {X : H → Type*}
    [∀ h, Fintype (X h)] (T : Tensor K U (∀ h, X h) (∀ i, V i))
    (read : Tag → ∀ i, V i → V i) :
    SiteRestriction (tagged (fun t c i => read t i (c i)) T) (diagonalControl (Tag := Tag) T) := by
  classical
  obtain ⟨A, M, P, eq, hM⟩ := tagged_eq_restrict_diagonal T read
  refine ⟨A, fun _ b d => if d = b then 1 else 0, P, ?_⟩
  convert eq using 2
  funext b d
  simp only [Fintype.prod_boole, ← funext_iff, hM]
  split_ifs <;> rfl

end LocalControl

/-- The tagged tensor used for the independent-diagonal lower restriction and the
tagged operator used for the upper restrictions agree coefficient by coefficient. -/
theorem tagged_sharedPower {H I J R UB UC : Type*} [Fintype J]
    {X : H → Type*} {Y : I → Type*} (perm : Tag → Equiv.Perm J)
    (P : UB → (∀ h, X h) → K) (Q : UC → (∀ i, Y i) → K) :
    PermutationStretch.tagged (R := R) perm P Q =
    tagged (fun t y i => ((y i).1 ∘ perm t, (y i).2 ∘ perm t))
      (PermutationStretch.sharedPower P Q) := rfl

/-- When `u,C` are grouped, the entire tagged sum is one linear map on that site. -/
def groupedCMap (readC : Tag → C → C) :
    ((U × C) → K) →ₗ[K] (((Tag × U) × C) → K) where
  toFun v := fun x => v (x.1.2, readC x.1.1 x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tagged_groupedC (readC : Tag → C → C) (T : Tensor K U B C) (b : B) :
    (fun x : (Tag × U) × C => tagged readC T x.1 b x.2) =
      groupedCMap readC (fun x => T x.1 b x.2) := rfl

section Product

variable {J L H I : Type*} [Fintype J] {X : H → Type*} {Y : I → Type*}

/-- An elementary product summand, with its power coordinates kept at each site. -/
def wordProduct (T : L → Tensor K U (∀ h, X h) (∀ i, Y i)) (s : J → L) :
    Tensor K (J → U) (∀ h, J → X h) (∀ i, J → Y i) :=
  fun u b c => ∏ j, T (s j) (u j) (fun h => b h j) (fun i => c i j)

/-- A product word in nonzero summands is nonzero. The nonzero coordinate of each
factor may be chosen independently. -/
theorem wordProduct_ne_zero [Nontrivial K] [NoZeroDivisors K]
    (T : L → Tensor K U (∀ h, X h) (∀ i, Y i)) (hT : ∀ l, T l ≠ 0) (s : J → L) :
    wordProduct T s ≠ 0 := by
  classical
  have witness (j : J) : ∃ u b c, T (s j) u b c ≠ 0 := by
    by_contra! hn
    exact hT (s j) (funext fun u => funext fun b => funext fun c => hn u b c)
  choose u b c hn using witness
  intro hz
  have hzero := congrFun (congrFun (congrFun hz u) (fun h j => b j h)) (fun i j => c j i)
  exact (Finset.prod_ne_zero_iff.mpr (fun j _ => hn j)) hzero

omit [Fintype J] in
/-- The tag remembers each permutation block, so a tagged nonzero product remains
nonzero even in positive characteristic. -/
theorem tagged_permutations_ne_zero [Nonempty Tag]
    (perm : Tag → Equiv.Perm J) (T : Tensor K U B (∀ i, J → Y i)) (hT : T ≠ 0) :
    tagged (fun t d i => d i ∘ perm t) T ≠ 0 := by
  classical
  obtain ⟨t⟩ := ‹Nonempty Tag›
  intro hzero
  apply hT
  funext u b c
  have h := congrFun (congrFun (congrFun hzero (t, u)) b) (fun i => c i ∘ (perm t).symm)
  simpa [tagged, Function.comp_assoc] using h

/-- The expansion of a tensor power into its product summands, in the original
coordinate spaces. -/
theorem power_sum_eq_sum_wordProduct [Fintype L] [DecidableEq J]
    (T : L → Tensor K U (∀ h, X h) (∀ i, Y i))
    (u : J → U) (b : ∀ h, J → X h) (c : ∀ i, J → Y i) :
    (∏ j, ∑ l, T l (u j) (fun h => b h j) (fun i => c i j)) =
      ∑ s : J → L, wordProduct T s u b c := Fintype.prod_sum _

/-- Expanding an ordinary-sum representation of the shared target gives its tagged
power as the sum of the tagged products bounded by the two upper restrictions.
Pairs of power coordinates and powers of pairs are identified by evaluation. -/
theorem tagged_sharedPower_eq_sum_wordProduct [Fintype L] [DecidableEq J]
    {R UB UC : Type*} (perm : Tag → Equiv.Perm J)
    (P : UB → (∀ h, X h) → K) (Q : UC → (∀ i, Y i) → K)
    (T : L → Tensor K (R × UB × UC) (∀ h, R × X h) (∀ i, R × Y i))
    (hsum : ∀ w u v (b : ∀ h, R × X h) (c : ∀ i, R × Y i),
      PermutationStretch.diagonalCoeff w (fun h => (b h).1) *
        PermutationStretch.diagonalCoeff w (fun i => (c i).1) *
        P u (fun h => (b h).2) * Q v (fun i => (c i).2) = ∑ l, T l (w, u, v) b c)
    (a : Tag × (J → R) × (J → UB) × (J → UC))
    (b : ∀ h, (J → R) × (J → X h)) (c : ∀ i, (J → R) × (J → Y i)) :
    PermutationStretch.tagged perm P Q a b c =
      ∑ s : J → L, tagged (fun t d i => d i ∘ perm t) (wordProduct T s)
        (a.1, fun j => (a.2.1 j, a.2.2.1 j, a.2.2.2 j))
        (fun h j => ((b h).1 j, (b h).2 j)) (fun i j => ((c i).1 j, (c i).2 j)) := by
  rcases a with ⟨tag, w, u, v⟩
  simp only [PermutationStretch.tagged, PermutationStretch.sharedPower_eq_prod, tagged,
    wordProduct, Function.comp_apply]
  let f (j : J) (l : L) := T l (w j, u j, v j) (fun h => ((b h).1 j, (b h).2 j))
    (fun i => ((c i).1 (perm tag j), (c i).2 (perm tag j)))
  refine Eq.trans ?_ (Fintype.prod_sum f)
  apply Finset.prod_congr rfl
  intro j _
  exact hsum _ _ _ (fun h => ((b h).1 j, (b h).2 j))
    (fun i => ((c i).1 (perm tag j), (c i).2 (perm tag j)))

/-- Moving a permutation from `C` to the other two blocks reorders the sequence. -/
theorem wordProduct_permuteC (T : L → Tensor K U (∀ h, X h) (∀ i, Y i)) (s : J → L)
    (π : Equiv.Perm J) (u : J → U) (b : ∀ h, J → X h) (c : ∀ i, J → Y i) :
    wordProduct T s u b (fun i => c i ∘ π) =
      wordProduct T (s ∘ π.symm) (u ∘ π.symm) (fun h => b h ∘ π.symm) c := by
  simpa [wordProduct, Function.comp_def] using
    Equiv.prod_comp π (fun j => T (s (π.symm j)) (u (π.symm j))
      (fun h => b h (π.symm j)) (fun i => c i j))

/-- Simultaneously reordering the factors of a product acts by coordinate
permutations separately at every site, so cannot increase its price. -/
theorem wordProduct_reorder_restriction [DecidableEq J] [Fintype H] [Fintype I] [Fintype U]
    [∀ h, Fintype (X h)] [∀ i, Fintype (Y i)]
    (T : L → Tensor K U (∀ h, X h) (∀ i, Y i)) (s : J → L) (π : Equiv.Perm J) :
    SiteRestriction (wordProduct T (s ∘ π.symm)) (wordProduct T s) := by
  classical
  let a (u : J → U) := u ∘ π
  let l (h : H) (b : J → X h) := b ∘ π
  let r (i : I) (c : J → Y i) := c ∘ π
  have heq : wordProduct T (s ∘ π.symm) =
      Tensor.pullback a (fun b h => l h (b h)) (fun c i => r i (c i)) (wordProduct T s) := by
    funext u b c
    symm
    simpa only [Tensor.pullback, a, l, r, wordProduct, Function.comp_apply,
      Equiv.symm_apply_apply] using
      Equiv.prod_comp π (fun j => T (s (π.symm j)) (u j) (fun h => b h j) (fun i => c i j))
  rw [heq]
  exact siteRestriction_pullback a l r _

/-- The single map on the grouped site `u,B` supplying all tags in the fiber of
one reordered sequence. A coefficient at an output tag is read from precisely one
basis coordinate and is zero if the tag belongs to another fiber. -/
def groupedBMap (perm : Tag → Equiv.Perm J) (s q : J → L) :
    (((J → U) × (∀ h, J → X h)) → K) →ₗ[K] (((Tag × (J → U)) × (∀ h, J → X h)) → K) := by
  classical
  exact
    { toFun := fun v x =>
        if s ∘ (perm x.1.1).symm = q then
          v (x.1.2 ∘ (perm x.1.1).symm, fun h => x.2 h ∘ (perm x.1.1).symm)
        else 0
      map_add' := by
        intro f g
        funext x
        split <;> simp_all
      map_smul' := by
        intro a f
        funext x
        split <;> simp_all }

/-- The tagged product is an ordinary sum of grouped-site restrictions, one for each
sequence `q`. The number of possible summands is `|L| ^ |J|`. -/
theorem tagged_wordProduct_eq_groupedB_sum [Fintype L] [DecidableEq J]
    (T : L → Tensor K U (∀ h, X h) (∀ i, Y i)) (s : J → L) (perm : Tag → Equiv.Perm J)
    (x : Tag × (J → U)) (b : ∀ h, J → X h) (c : ∀ i, J → Y i) :
    tagged (fun t d i => d i ∘ perm t) (wordProduct T s) x b c =
      ∑ q : J → L, groupedBMap perm s q
        (fun v => wordProduct T q v.1 v.2 c) (x, b) := by
  classical
  simp [tagged, groupedBMap, wordProduct_permuteC T s (perm x.1) x.2 b c]

end Product
end
end PermutationControl

end SpectralBooks
end LinearAlgebra
end OAI
