import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-! # Zero pins on padded packet slots

The live wire positions form an arbitrary embedded subset of the padded slots.
Restriction and extension by zero identify assignments on the live wires with
exactly the assignments satisfying the pins. For two independently summed ends,
the equality factors and the pins leave one common assignment per live word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open scoped BigOperators Classical

variable {A B R : Type*}

/-- Insert the live bits at their selected slots and put zero in every unused slot. -/
noncomputable def zeroExtend (e : A ↪ B) (w : A → Bool) : B → Bool :=
  Function.extend e w (fun _ => false)

/-- The extended assignment agrees with the original bit in each live slot. -/
@[simp] theorem zeroExtend_image (e : A ↪ B) (w : A → Bool) (a : A) :
    zeroExtend e w (e a) = w a := e.injective.extend_apply w _ a

/-- An unused position receives the pinned bit zero. -/
theorem zeroExtend_unused (e : A ↪ B) (w : A → Bool) {b : B} (h : b ∉ Set.range e) :
    zeroExtend e w b = false := Function.extend_apply' w _ b h

/-- Restricting the zero extension to live positions gives back the entire assignment. -/
@[simp] theorem zeroExtend_restrict (e : A ↪ B) (w : A → Bool) : zeroExtend e w ∘ e = w :=
  funext (zeroExtend_image e w)

/-- A padded assignment that satisfies all unused pins is reconstructed by restriction. -/
theorem zeroExtend_of_pinned (e : A ↪ B) (w : B → Bool)
    (h : ∀ b ∉ Set.range e, w b = false) : zeroExtend e (w ∘ e) = w := by
  funext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    exact zeroExtend_image e _ a
  · exact (zeroExtend_unused e _ hb).trans (h b hb).symm

/-- Boolean words on live wires are in bijection with all pinned padded words. -/
noncomputable def zeroPinnedEquiv (e : A ↪ B) :
    (A → Bool) ≃ {w : B → Bool // ∀ b ∉ Set.range e, w b = false} where
  toFun w := ⟨zeroExtend e w, fun _ h => zeroExtend_unused e w h⟩
  invFun w := w.val ∘ e
  left_inv := zeroExtend_restrict e
  right_inv w := Subtype.ext (zeroExtend_of_pinned e w.val w.property)

/-- Summing over the padded words with all unused bits pinned to zero retains
exactly one copy of each original word's weight. -/
theorem sum_pinned [Fintype A] [Fintype B] [AddCommMonoid R]
    (e : A ↪ B) (weight : (A → Bool) → R) :
    (∑ a : B → Bool, if (∀ s ∉ Set.range e, a s = false) then weight (a ∘ e) else 0) =
      ∑ y : A → Bool, weight y := by
  symm
  apply Fintype.sum_of_injective (zeroExtend e)
  · intro u v h
    simpa only [zeroExtend_restrict] using congrArg (fun w : B → Bool => w ∘ e) h
  · intro w hw
    apply ite_eq_right
    intro hp
    exact hw ⟨w ∘ e, zeroExtend_of_pinned e w hp⟩
  · intro y
    rw [ite_eq_left (fun _ h => zeroExtend_unused e y h), zeroExtend_restrict]

private theorem product_of_tests [Fintype B] [CommSemiring R] (P : B → Prop) [DecidablePred P] :
    (∏ b : B, if P b then (1 : R) else 0) = if ∀ b, P b then 1 else 0 := by
  by_cases h : ∀ b, P b
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨b, hb⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ b) (ite_eq_right hb)

private theorem pins_iff (e : A ↪ B) (w : B → Bool) :
    (∀ s, s ∈ Set.range e ∨ w s = false) ↔ ∀ s ∉ Set.range e, w s = false := by
  constructor
  · intro h s hs
    exact (h s).resolve_left hs
  · intro h s
    by_cases hs : s ∈ Set.range e
    · exact Or.inl hs
    · exact Or.inr (h s hs)

/-- Independent source and destination words with an equality wire in each
slot and zero pins at both unused ends give the original single-wire sum.
The weight can depend arbitrarily on both full padded assignments. -/
theorem sum_padded_ends [Fintype A] [Fintype B] [CommSemiring R]
    (e : A ↪ B) (weight : (B → Bool) → (B → Bool) → R) :
    (∑ x : B → Bool, ∑ y : B → Bool,
      weight x y * (∏ s : B, if x s = y s then 1 else 0) *
      (∏ s : B, if s ∈ Set.range e ∨ x s = false then 1 else 0) *
      (∏ s : B, if s ∈ Set.range e ∨ y s = false then 1 else 0)) =
      ∑ w : A → Bool, weight (zeroExtend e w) (zeroExtend e w) := by
  rw [← sum_pinned e (fun w => weight (zeroExtend e w) (zeroExtend e w))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · rw [product_of_tests (R := R) (fun s => x s = x s), ite_eq_left (fun _ => rfl), mul_one,
      product_of_tests (R := R) (fun s => s ∈ Set.range e ∨ x s = false)]
    by_cases hx : ∀ s ∉ Set.range e, x s = false
    · rw [ite_eq_left ((pins_iff e x).mpr hx), ite_eq_left hx, mul_one, mul_one, zeroExtend_of_pinned e x hx]
    · rw [ite_eq_right (mt (pins_iff e x).mp hx), ite_eq_right hx, mul_zero]
  · intro y _ hy
    have he : ¬∀ s, x s = y s := fun h => hy (funext h).symm
    rw [product_of_tests (R := R) (fun s => x s = y s), ite_eq_right he, mul_zero, zero_mul, zero_mul]
  · simp

end Cube.Physical

end BorderVNP
end Computability
end OAI
