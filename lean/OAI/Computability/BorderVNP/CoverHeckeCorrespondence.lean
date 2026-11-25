import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Group

/-!
# The Hecke correspondence on the frame quotient

Lemma 5.2 of the border lower-bound paper uses right cosets, written
`Γ ∖ G`. The branches at a representative `x` are indexed by the right
cosets of the intersection subgroup in `Γ`. Their **sum** descends
to the frame quotient. The branch indexed by the identity is left
translation by the particular element `z`.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open Finset

variable {G : Type*} [Group G]

/-- The space of right cosets, with the subgroup acting on the left. -/
abbrev Cosets (Γ : Subgroup G) := Quotient (QuotientGroup.rightRel Γ)

/-- The right coset containing a representative. -/
abbrev coset (Γ : Subgroup G) (x : G) : Cosets Γ := Quotient.mk _ x

/-- The subgroup of `Γ` consisting of the elements conjugated back into `Γ` by `z`. -/
def intersection (Γ : Subgroup G) (z : G) : Subgroup Γ :=
  Γ.comap ((MulAut.conj z).toMonoidHom.comp Γ.subtype)

/-- Right multiplication acts on the right cosets by permutations. -/
def rightMul (Γ : Subgroup G) (y : G) : Cosets Γ ≃ Cosets Γ where
  toFun := Quotient.map (· * y) fun _ _ h => QuotientGroup.rightRel_apply.mpr (by
    simpa [mul_assoc] using QuotientGroup.rightRel_apply.mp h)
  invFun := Quotient.map (· * y⁻¹) fun _ _ h => QuotientGroup.rightRel_apply.mpr (by
    simpa [mul_assoc] using QuotientGroup.rightRel_apply.mp h)
  left_inv := by rintro ⟨x⟩; change coset _ (x * y * y⁻¹) = coset Γ x; simp
  right_inv := by rintro ⟨x⟩; change coset _ (x * y⁻¹ * y) = coset Γ x; simp

/-- The individual branches are independent of the representatives of their *indices*. -/
def branch (Γ : Subgroup G) (z x : G) : Cosets (intersection Γ z) → Cosets Γ :=
  Quotient.lift (fun a : Γ => coset Γ (z * a * x)) fun a b h => by
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have hi := QuotientGroup.rightRel_apply.mp h
    change z * ((b : G) * (a : G)⁻¹) * z⁻¹ ∈ Γ at hi
    simpa [mul_assoc] using hi

/-- The identity-index branch recovers the action of `z`. -/
theorem branch_identity (Γ : Subgroup G) (z x : G) :
    branch Γ z x (coset (intersection Γ z) 1) = coset Γ (z * x) := by
  change coset Γ (z * 1 * x) = _
  rw [mul_one]

/-- Changing the frame representative permutes the branches. -/
theorem branch_translate (Γ : Subgroup G) (z x : G) (a : Γ)
    (i : Cosets (intersection Γ z)) :
    branch Γ z (a * x) i = branch Γ z x (rightMul (intersection Γ z) a i) := by
  rcases i with ⟨b⟩
  change coset Γ (z * b * (a * x)) = coset Γ (z * ((b * a : Γ) : G) * x)
  simp [mul_assoc]

/-- Any symmetric sum of branch values is invariant under changing the frame representative. -/
theorem sum_branches_translate {M : Type*} [AddCommMonoid M] (Γ : Subgroup G)
    (z x : G) [Fintype (Cosets (intersection Γ z))] (a : Γ) (f : Cosets Γ → M) :
    ∑ i, f (branch Γ z (a * x) i) = ∑ i, f (branch Γ z x i) := by
  simp_rw [branch_translate Γ z x a]
  exact Equiv.sum_comp (rightMul (intersection Γ z) a) (fun i => f (branch Γ z x i))

/-- The finite Hecke average on the actual quotient, with normalized weights. -/
noncomputable def average (Γ : Subgroup G) (z : G) [Fintype (Cosets (intersection Γ z))]
    (f : Cosets Γ → ℝ) : Cosets Γ → ℝ :=
  Quotient.lift (fun x => (Fintype.card (Cosets (intersection Γ z)) : ℝ)⁻¹ *
    ∑ i, f (branch Γ z x i)) fun a b h => by
      congr 1
      let γ : Γ := ⟨b * a⁻¹, QuotientGroup.rightRel_apply.mp h⟩
      have hγ : (γ : G) * a = b := by simp [γ]
      rw [← hγ]
      exact (sum_branches_translate Γ z a γ f).symm

/-- Evaluation of the descended average at a representative. -/
theorem average_coset (Γ : Subgroup G) (z x : G) [Fintype (Cosets (intersection Γ z))]
    (f : Cosets Γ → ℝ) :
    average Γ z f (coset Γ x) = (Fintype.card (Cosets (intersection Γ z)) : ℝ)⁻¹ *
      ∑ i, f (branch Γ z x i) := rfl

end Hecke

end BorderVNP
end Computability
end OAI
