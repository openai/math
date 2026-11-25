import OAI.LinearAlgebra.TensorSpectrum.Additive.States
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Projective

/-!
# State preservation by normalized multiplication

The order hypotheses here are the concrete tensor restriction properties. In
particular the lower bound on nonzero tensors proves the denominator is positive;
it is not a separate premise about a proposed character.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

open Set

variable {S : Type*} [CommSemiring S] [PartialOrder S]

theorem state_one_le {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : 1 ≤ f z := by
  simpa only [hf.2.1] using hf.2.2.2.1 (hunit z hz)

theorem state_pos {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : 0 < f z :=
  lt_of_lt_of_le zero_lt_one (state_one_le hf hunit hz)

/-- Every projective map preserves all five defining state conditions, including
the detecting inequalities for every tensor. -/
theorem projective_mem_stateSet {T : S} {k : ℕ} {f : S → ℝ}
    (hf : f ∈ stateSet T k) (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    {z : S} (hz : z ≠ 0) : projective z f ∈ stateSet T k := by
  have hpos : 0 < f z := state_pos hf hunit hz
  refine ⟨projective_zero z f hf.1, projective_one z f hpos.ne', ?_, ?_, ?_⟩
  · intro x y
    change f (z * (x + y)) / f z = f (z * x) / f z + f (z * y) / f z
    rw [mul_add, hf.2.2.1, add_div]
  · intro x y hxy
    exact div_le_div_of_nonneg_right (hf.2.2.2.1 (hmul z hxy)) hpos.le
  · intro s
    change (k : ℝ) * (f (z * s) / f z) ≤ f (z * (T * s)) / f z
    rw [show z * (T * s) = T * (z * s) by ac_rfl, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf.2.2.2.2 (z * s)) hpos.le

theorem projective_mapsTo_stateSet (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (hmul : ∀ z : S, Monotone (fun x : S => z * x))
    {z : S} (hz : z ≠ 0) :
    MapsTo (projective z) (stateSet T k) (stateSet T k) :=
  fun _ hf => projective_mem_stateSet hf hunit hmul hz

theorem projective_continuousOn_stateSet (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    {z : S} (hz : z ≠ 0) : ContinuousOn (projective z) (stateSet T k) :=
  continuousOn_projective z (stateSet T k) fun _ hf => (state_pos hf hunit hz).ne'

/-- A simultaneous fixed point of the actual state maps is a monotone semiring
character, and the detection inequality at the unit yields its required value. -/
theorem character_of_common_fixedPoint (T : S) (k : ℕ)
    (hunit : ∀ z : S, z ≠ 0 → 1 ≤ z)
    (f : S → ℝ) (hf : f ∈ stateSet T k)
    (hfixed : ∀ z : S, z ≠ 0 → projective z f = f) :
    ∃ χ : S →+* ℝ, Monotone χ ∧ (k : ℝ) ≤ χ T ∧ ∀ x, χ x = f x := by
  have hmul : ∀ x y : S, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x = 0
    · simp [hx, hf.1]
    · exact (projective_fixed_iff x f (state_pos hf hunit hx).ne').mp (hfixed x hx) y
  let χ : S →+* ℝ :=
    { toFun := f
      map_zero' := hf.1
      map_one' := hf.2.1
      map_add' := hf.2.2.1
      map_mul' := hmul }
  refine ⟨χ, hf.2.2.2.1, ?_, fun _ => rfl⟩
  change (k : ℝ) ≤ f T
  simpa only [mul_one, hf.2.1] using hf.2.2.2.2 1

end OAI.LinearAlgebra.TensorSpectrum
