import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Replacing a wire identity inside a contraction

The identity used by a compression step applies to half-wire indices at
the old sites. Each term may choose a different placement of the old
sites. After the replacement, a site and all its open inputs occur together
in one new factor.
-/

namespace ThreeFlat.Diagonal

variable {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
variable {X : I → Type*} [∀ i, Fintype (X i)]

/-- Split the old half-wire indices by the destination of their sites. -/
def sitesByGroup {G : Type*} (owner : I → G) :
    (∀ i, X i) ≃ (∀ g, ∀ i : {i // owner i = g}, X i) where
  toFun v _ i := v i
  invFun a i := a (owner i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv a := by
    funext g i
    rcases i with ⟨i, rfl⟩
    rfl

/-- A wire expansion with term-dependent placement can be performed around
arbitrary old site factors. The resulting formula needs no shared copies of
their private or external inputs. -/
theorem contraction_wire_rewrite [DecidableEq I] {H : Type*} [Fintype H]
    {G Z : H → Type*} [∀ h, Fintype (G h)] [∀ h, DecidableEq (G h)] [∀ h, Fintype (Z h)]
    (owner : ∀ h, I → G h) (wire : (∀ i, X i) → F)
    (kernel : ∀ h g, Z h → (∀ i : {i // owner h i = g}, X i) → F)
    (entry : ∀ x, wire x = ∑ h, ∑ z, ∏ g, kernel h g z (fun i => x i))
    (factor : ∀ i, X i → F) :
    (∑ x : ∀ i, X i, wire x * ∏ i, factor i (x i)) =
      ∑ h, ∑ z, ∏ g, ∑ a : ∀ i : {i // owner h i = g}, X i,
        kernel h g z a * ∏ i : {i // owner h i = g}, factor i (a i) := by
  classical
  simp_rw [entry, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_sum]
  let e := sitesByGroup (X := X) (owner h)
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  change (∏ g, kernel h g z (fun i => e.symm a i)) *
      (∏ i, factor i (e.symm a i)) = _
  rw [Finset.prod_mul_distrib]
  congr 1
  · apply Finset.prod_congr rfl
    intro g _
    congr 1
    funext i
    rcases i with ⟨i, rfl⟩
    rfl
  · rw [← Fintype.prod_fiberwise (owner h) (fun i => factor i (e.symm a i))]
    apply Finset.prod_congr rfl
    intro g _
    apply Finset.prod_congr rfl
    intro i _
    rcases i with ⟨i, rfl⟩
    rfl

end ThreeFlat.Diagonal

end OAI
