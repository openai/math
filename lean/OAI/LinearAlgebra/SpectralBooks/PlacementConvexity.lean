import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Tactic

/-! # Consequences of convexity of placed diagonal prices

A finite list of synchronized straight-line interpolations is recorded by its
finite set of endpoint pairs. Duplicates at an occupied site have no effect
on the diagonal price. In a homogeneous flat, the midpoint inequality for
all pairs of vertices implies subadditivity for Minkowski addition.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- Joint convexity of diagonal prices along synchronized straight lines. -/
def JointlyConvexPrice (δ : Finset E → ℝ) : Prop :=
  ∀ (P : Finset (E × E)), P.Nonempty → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    δ (P.image fun p ↦ a • p.1 + b • p.2) ≤
      a * δ (P.image Prod.fst) + b * δ (P.image Prod.snd)

/-- On a homogeneous flat, interpolating a list indexed by the full product of
two vertex sets gives the subadditive inequality for their Minkowski sum. -/
theorem price_add_le_of_jointConvex (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hscale : ∀ (S : Finset E), S.Nonempty → ∀ r : ℝ, 0 < r →
      δ (S.image (r • ·)) = r * δ S) (S T : Finset E) (hS : S.Nonempty) (hT : T.Nonempty) :
    δ (S + T) ≤ δ S + δ T := by
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have h := hjoint (S ×ˢ T) (hS.product hT) r r hr.le hr.le (by norm_num [r])
  have himage : (S ×ˢ T).image (fun p ↦ r • p.1 + r • p.2) = (S + T).image (r • ·) := by
    simp only [Finset.add_def, Finset.image_image, Function.comp_def, smul_add]
  rw [himage, hscale _ (hS.add hT) r hr, Finset.product_image_fst hT,
    Finset.product_image_snd hS] at h
  dsimp [r] at h
  linarith

omit [Module ℝ E] in
/-- Adding a singleton gives a translate, and adding its negative translates back. -/
theorem price_translate_of_add_le (δ : Finset E → ℝ)
    (hsubadd : ∀ (S T : Finset E), S.Nonempty → T.Nonempty → δ (S + T) ≤ δ S + δ T)
    (hsingle : ∀ x : E, δ {x} = 0) (S : Finset E) (hS : S.Nonempty) (v : E) :
    δ (S + {v}) = δ S := by
  apply le_antisymm
  · simpa [hsingle] using hsubadd S {v} hS (Finset.singleton_nonempty _)
  · have h := hsubadd (S + {v}) {-v} (hS.add (Finset.singleton_nonempty _))
        (Finset.singleton_nonempty _)
    simpa only [add_assoc, Finset.singleton_add_singleton, add_neg_cancel, hsingle, add_zero,
      show ({0} : Finset E) = 0 by rfl] using h

/-- Adjoining a point in the convex hull leaves a monotone, jointly convex
diagonal price unchanged. -/
theorem price_insert_of_mem_convexHull (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (S : Finset E) (hS : S.Nonempty) {z : E} (hz : z ∈ convexHull ℝ (S : Set E)) :
    δ (insert z S) = δ S := by
  refine le_antisymm (?_ : z ∈ {w : E | δ (insert w S) ≤ δ S})
    (hmono hS (Finset.subset_insert _ _))
  apply convexHull_min (t := {w : E | δ (insert w S) ≤ δ S}) _ _ hz
  · intro x hx
    simp [Finset.insert_eq_of_mem hx]
  · intro x hx y hy a b ha hb hab
    let P := S.image (fun s ↦ (s, s))
    have h := hjoint (insert (x, y) P) (Finset.insert_nonempty _ _) a b ha hb hab
    have hid (s : E) : a • s + b • s = s := by rw [← add_smul, hab, one_smul]
    simp [P, Finset.image_image, Function.comp_def, hid] at h
    change δ (insert (a • x + b • y) S) ≤ δ S
    change δ (insert x S) ≤ δ S at hx
    change δ (insert y S) ≤ δ S at hy
    calc
      _ ≤ a * δ (insert x S) + b * δ (insert y S) := h
      _ ≤ a * δ S + b * δ S := add_le_add
        (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- Adjoining a finite family of points in the convex hull preserves price. -/
theorem price_union_of_subset_convexHull (δ : Finset E → ℝ) (hjoint : JointlyConvexPrice δ)
    (hmono : ∀ ⦃S T : Finset E⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (S T : Finset E) (hS : S.Nonempty) (hT : (T : Set E) ⊆ convexHull ℝ (S : Set E)) :
    δ (S ∪ T) = δ S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert z T hz ih =>
    have hzS := hT (Finset.mem_insert_self z T)
    have hT' := fun y (hy : y ∈ T) ↦ hT (Finset.mem_insert_of_mem hy)
    have hsub : (S : Set E) ⊆ ↑(S ∪ T) := Finset.subset_union_left
    rw [Finset.union_insert, price_insert_of_mem_convexHull δ hjoint hmono _
      (hS.mono Finset.subset_union_left) (convexHull_mono hsub hzS), ih hT']

end SpectralBooks
end LinearAlgebra
end OAI
