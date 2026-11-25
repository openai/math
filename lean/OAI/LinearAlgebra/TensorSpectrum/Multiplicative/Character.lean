import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.FixedPoint
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Finite
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.States
import Mathlib.Basic.NNReal.Defs

/-!
# Multiplicativity of a compact convex tensor-state space

This is Appendix A.2, including the single-map fixed-point existence step.
The projective fixed-point result is proved by finite weighted orbit averages,
so no Schauder theorem is postulated. Nonemptiness of the additive state space
is the explicit Appendix A.1 input; no multiplicative state is an input.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set
open scoped NNReal

section Monoid

variable {S : Type*} [CommMonoidWithZero S]

theorem multiplicative_point_of_compact_convex
    (K : Set (S → ℝ)) (B : S → ℝ)
    (hK : K.Nonempty) (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hzero : ∀ f ∈ K, f 0 = 0) (hunit : ∀ f ∈ K, f 1 = 1)
    (hbound : ∀ f ∈ K, ∀ x, 0 ≤ f x ∧ f x ≤ B x)
    (hlower : ∀ f ∈ K, ∀ z : S, z ≠ 0 → 1 ≤ f z)
    (hinvariant : ∀ z : S, z ≠ 0 → MapsTo (projective z) K K) :
    ∃ f ∈ K, ∀ z x, f (z * x) = f z * f x := by
  apply multiplicative_of_finite_common_points K hcompact hzero
  apply finite_common_points_of_slice_fixedPoints K hK hcompact hconvex hunit
    (fun f hf z hz => (zero_lt_one.trans_le (hlower f hf z hz)).ne') hinvariant
  intro L hLK hL hLc hLv hLi z hz
  exact projective_fixedPoint_of_compact_convex L z B hL hLc hLv
    (fun f hf => hunit f (hLK hf))
    (fun f hf => hbound f (hLK hf))
    (fun f hf => hlower f (hLK hf) z hz) (hLi z hz)

end Monoid

section Semiring

variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- Appendix A.2 turns an actual nonempty additive detecting state space into a
monotone real semiring character without assuming a character or fixed point. -/
theorem exists_character_of_nonempty_stateSet
    (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hR : ∀ x : S, x ≤ (R x : S))
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    (hnonempty : (stateSet T k).Nonempty) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (k : ℝ) ≤ χ T := by
  have hbound : ∀ f ∈ stateSet T k, ∀ x, 0 ≤ f x ∧ f x ≤ (R x : ℝ) :=
    fun f hf => stateSet_subset_coordinateBox T k R hzero hR hf
  obtain ⟨f, hf, hfmul⟩ := multiplicative_point_of_compact_convex (stateSet T k)
    (fun x => (R x : ℝ)) hnonempty (stateSet_isCompact T k R hzero hR)
    (stateSet_convex T k) (fun _ hf => hf.1) (fun _ hf => hf.2.1) hbound
    (fun f hf z hz => state_one_le hf hunit hz)
    (fun z hz => projective_mapsTo_stateSet T k hunit hmul hz)
  have hfixed : ∀ z : S, z ≠ 0 → projective z f = f := by
    intro z hz
    exact (projective_fixed_iff z f (state_pos hf hunit hz).ne').mpr (hfmul z)
  obtain ⟨χ, hmono, hdetect, _⟩ := character_of_common_fixedPoint T k hunit f hf hfixed
  exact ⟨χ, hmono, hdetect⟩

/-- The same character with its nonnegative codomain made explicit. -/
theorem exists_nnreal_character_of_nonempty_stateSet
    (T : S) (k : ℕ) (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hR : ∀ x : S, x ≤ (R x : S))
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    (hnonempty : (stateSet T k).Nonempty) :
    ∃ χ : S →+* ℝ≥0, Monotone χ ∧ (k : ℝ≥0) ≤ χ T := by
  obtain ⟨χ, hmono, hk⟩ := exists_character_of_nonempty_stateSet T k R
    hzero hunit hR hmul hnonempty
  have hnonneg : ∀ x, 0 ≤ χ x := by
    intro x
    simpa only [map_zero] using hmono (hzero x)
  let ψ : S →+* ℝ≥0 :=
    { toFun := fun x => ⟨χ x, hnonneg x⟩
      map_zero' := by apply Subtype.ext; exact map_zero χ
      map_one' := by apply Subtype.ext; exact map_one χ
      map_add' := by intro x y; apply Subtype.ext; exact map_add χ x y
      map_mul' := by intro x y; apply Subtype.ext; exact map_mul χ x y }
  refine ⟨ψ, fun _ _ h => hmono h, ?_⟩
  change ((k : ℝ≥0) : ℝ) ≤ χ T
  simpa only [NNReal.coe_natCast] using hk

end Semiring

end OAI.LinearAlgebra.TensorSpectrum
