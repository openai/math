import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# The independent diagonals in the permutation stretch

Write the sites as a common site `u` and two families `B`, `C`. The other sites
carry one-dimensional spaces. We keep the coordinates at *each* site of each
family. A tagged permutation acts on the power factors at all sites of `C`.
A local map at `u` reads the tag chosen for a pair of words and completes the
permutation of the private `C` tensor. This yields equation `doubling-independent`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

open scoped BigOperators Classical
open MatrixMultiplication.Foundation

section

variable {K B C : Type*} [CommSemiring K]

/-- An ordinary restriction, with a separate matrix at every site of `B` and `C`. -/
def SiteRestriction [Fintype B] [Fintype C]
    {U U' : Type*} {X X' : B → Type*} {Y Y' : C → Type*}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (target : Tensor K U' (∀ b, X' b) (∀ c, Y' c))
    (source : Tensor K U (∀ b, X b) (∀ c, Y c)) : Prop :=
  ∃ (A : U' → U → K) (L : ∀ b, X' b → X b → K) (R : ∀ c, Y' c → Y c → K),
    target = Tensor.restrict A (fun x' x => ∏ b, L b (x' b) (x b))
      (fun y' y => ∏ c, R c (y' c) (y c)) source

/-- Choosing one input coordinate for each output coordinate, independently at each
site, gives an ordinary tensor restriction over any commutative semiring. -/
theorem siteRestriction_pullback [Fintype B] [Fintype C]
    {U U' : Type*} {X X' : B → Type*} {Y Y' : C → Type*}
    [Fintype U] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (a : U' → U) (l : ∀ b, X' b → X b) (r : ∀ c, Y' c → Y c)
    (T : Tensor K U (∀ b, X b) (∀ c, Y c)) :
    SiteRestriction (Tensor.pullback a (fun x b => l b (x b)) (fun y c => r c (y c)) T) T := by
  classical
  refine ⟨fun u' u => if u = a u' then 1 else 0,
    fun b x' x => if x = l b x' then 1 else 0,
    fun c y' y => if y = r c y' then 1 else 0, ?_⟩
  rw [Tensor.pullback_eq_restrict]
  simp_rw [Fintype.prod_boole, ← funext_iff]

namespace PermutationStretch

variable {M R W Tag UB UC : Type*} {X : B → Type*} {Y : C → Type*}

/-- A power of a private tensor, keeping its power coordinates at the original sites. -/
def privatePower [Fintype M] (P : UB → (∀ b, X b) → K)
    (u : M → UB) (x : ∀ b, M → X b) : K := ∏ t, P (u t) (fun b => x b t)

/-- Simultaneous permutation at every occupied site fixes a tensor power. -/
theorem privatePower_perm [Fintype M] (P : UB → (∀ b, X b) → K)
    (π : Equiv.Perm M) (u : M → UB) (x : ∀ b, M → X b) :
    privatePower P (u ∘ π) (fun b => x b ∘ π) = privatePower P u x :=
  Equiv.prod_comp π (fun t => P (u t) (fun b => x b t))

/-- A common diagonal on the center and every site of one side of the book. -/
noncomputable def diagonalCoeff (w : W) (x : B → W) : K := by
  classical
  exact if ∀ b, x b = w then 1 else 0

/-- The coefficient of `X^⊗m`, with word coordinates grouped separately from the
coordinates of the two private powers. -/
def sharedPower [Fintype M] (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    Tensor K ((M → R) × (M → UB) × (M → UC))
      (∀ b, (M → R) × (M → X b)) (∀ c, (M → R) × (M → Y c)) :=
  fun u x y =>
    diagonalCoeff u.1 (fun b => (x b).1) * diagonalCoeff u.1 (fun c => (y c).1) *
    privatePower P u.2.1 (fun b => (x b).2) * privatePower Q u.2.2 (fun c => (y c).2)

private theorem diagonalCoeff_power [Fintype M] (w : M → R) (x : B → M → R) :
    (∏ t, diagonalCoeff (K := K) (w t) (fun b => x b t)) = diagonalCoeff w x := by
  classical
  have h : (∀ t b, x b t = w t) ↔ ∀ b, x b = w :=
    ⟨fun h b => funext (fun t => h t b), fun h t b => congrFun (h b) t⟩
  simp only [diagonalCoeff, Fintype.prod_boole, h]

/-- The shared power is exactly the sitewise product of `m` copies of a single
common diagonal times the two original private tensors. -/
theorem sharedPower_eq_prod [Fintype M] (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K)
    (w : M → R) (u : M → UB) (v : M → UC)
    (x : ∀ b, (M → R) × (M → X b)) (y : ∀ c, (M → R) × (M → Y c)) :
    sharedPower P Q (w, u, v) x y =
      ∏ t, diagonalCoeff (w t) (fun b => (x b).1 t) * diagonalCoeff (w t) (fun c => (y c).1 t) *
        P (u t) (fun b => (x b).2 t) * Q (v t) (fun c => (y c).2 t) := by
  simp only [sharedPower, privatePower, Finset.prod_mul_distrib, diagonalCoeff_power]

/-- Tag each permutation at the center and permute its power coordinates at each
site of `C`. Evaluating a coefficient with a fixed tag selects exactly its summand. -/
def tagged [Fintype M] (π : Tag → Equiv.Perm M)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    Tensor K (Tag × (M → R) × (M → UB) × (M → UC))
      (∀ b, (M → R) × (M → X b)) (∀ c, (M → R) × (M → Y c)) :=
  fun u x y => sharedPower P Q u.2 x
    (fun c => ((y c).1 ∘ π u.1, (y c).2 ∘ π u.1))

/-- The two private powers times two independent `W`-diagonals, one on each side. -/
def independent [Fintype M] (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    Tensor K (W × W × (M → UB) × (M → UC))
      (∀ b, W × (M → X b)) (∀ c, W × (M → Y c)) :=
  fun u x y =>
    diagonalCoeff u.1 (fun b => (x b).1) * diagonalCoeff u.2.1 (fun c => (y c).1) *
    privatePower P u.2.2.1 (fun b => (x b).2) * privatePower Q u.2.2.2 (fun c => (y c).2)

/-- Equation `doubling-independent`. The covering property asks for one permutation
per ordered pair of words. An embedding allows the balanced words `W` to be a
proper subset of the full set `M → R` of diagonal labels. -/
theorem independent_restriction [Fintype B] [Fintype C] [Fintype M] [DecidableEq M] [Fintype R]
    [Fintype Tag] [Fintype UB] [Fintype UC] [∀ b, Fintype (X b)] [∀ c, Fintype (Y c)]
    (word : W ↪ (M → R)) (π : Tag → Equiv.Perm M)
    (cover : ∀ i j, ∃ k, word j ∘ π k = word i)
    (P : UB → (∀ b, X b) → K) (Q : UC → (∀ c, Y c) → K) :
    SiteRestriction (independent (M := M) (W := W) P Q) (tagged (R := R) π P Q) := by
  classical
  choose k hk using cover
  let center : W × W × (M → UB) × (M → UC) → Tag × (M → R) × (M → UB) × (M → UC) :=
    fun ⟨i, j, u, v⟩ => (k i j, word i, u, v ∘ π (k i j))
  let left : ∀ b, W × (M → X b) → (M → R) × (M → X b) := fun _ x => (word x.1, x.2)
  let right : ∀ c, W × (M → Y c) → (M → R) × (M → Y c) := fun _ y => (word y.1, y.2)
  have e : independent (M := M) (W := W) P Q = Tensor.pullback center
      (fun x b => left b (x b)) (fun y c => right c (y c)) (tagged π P Q) := by
    funext ⟨i, j, u, v⟩ x y
    have hpair (z : W) : word z ∘ π (k i j) = word i ↔ z = j := by
      rw [← hk i j]
      constructor
      · exact fun h => word.injective (funext (fun t => by simpa using congrFun h ((π (k i j)).symm t)))
      · rintro rfl; rfl
    simp only [independent, Tensor.pullback, center, left, right, tagged, sharedPower,
      diagonalCoeff, Function.Embedding.apply_eq_iff_eq, hpair, privatePower_perm]
    split_ifs <;> rfl
  rw [e]
  exact siteRestriction_pullback center left right _

end PermutationStretch
end

end

end SpectralBooks
end LinearAlgebra
end OAI
