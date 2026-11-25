import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer phases and weights for auxiliary separation

The phase modulus `5M` has no nonzero multiple on the label interval. After
projection, the Laurent weight is a square and vanishes exactly when the
sector guess and the auxiliary labels agree. These are local identities;
they do not assert the tensor separation or its tag inequality.
-/

namespace OAI.LinearAlgebra.TensorSpectrum.Separation

theorem dvd_iff_eq_zero_of_bounds (N x : ℤ) (hN : 0 < N)
    (hlo : -N < x) (hhi : x < N) : (N ∣ x ↔ x = 0) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hzero : k = 0
    · simp [hzero] at hk
      exact hk
    · rcases lt_or_gt_of_ne hzero with hneg | hpos
      · have hmul := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) hN.le
        nlinarith
      · have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ k by omega) hN.le
        nlinarith
  · rintro rfl
    exact dvd_zero N

/-- The paper's one-based label convention. -/
theorem projection_does_not_wrap
    (M h g u v : ℤ)
    (hM : 1 ≤ M) (hh0 : 1 ≤ h) (hhM : h ≤ M)
    (hg0 : 1 ≤ g) (hgM : g ≤ M)
    (hu0 : 1 ≤ u) (huM : u ≤ M)
    (hv0 : 1 ≤ v) (hvM : v ≤ M) :
    ((5 * M ∣ u - v + 2 * (g - h)) ↔ u - v + 2 * (g - h) = 0) := by
  exact dvd_iff_eq_zero_of_bounds (5 * M) (u - v + 2 * (g - h))
    (by omega) (by omega) (by omega)

/-- The same no-wrap property for finite labels numbered from zero. -/
theorem projection_does_not_wrap_fin {M : ℕ} (h g u v : Fin M) :
    ((5 * (M : ℤ) ∣ (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val)) ↔
      (u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val) = 0) := by
  have hh := h.isLt
  have hg := g.isLt
  have hu := u.isLt
  have hv := v.isLt
  exact dvd_iff_eq_zero_of_bounds (5 * (M : ℤ))
    ((u.val : ℤ) - v.val + 2 * ((g.val : ℤ) - h.val))
    (by omega) (by omega) (by omega)

/-- The weight identity is independent of the choice of zero- or one-based
labels. -/
theorem projected_square_weight
    (h g u v : ℤ) (hphase : u - v + 2 * (g - h) = 0) :
    g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2 ∧
    0 ≤ g ^ 2 + h * u - h ^ 2 - h * v ∧
    (g ^ 2 + h * u - h ^ 2 - h * v = 0 ↔ g = h ∧ u = v) := by
  have hweight : g ^ 2 + h * u - h ^ 2 - h * v = (g - h) ^ 2 := by
    calc
      g ^ 2 + h * u - h ^ 2 - h * v =
          (g - h) ^ 2 + h * (u - v + 2 * (g - h)) := by ring
      _ = (g - h) ^ 2 := by rw [hphase]; ring
  refine ⟨hweight, ?_, ?_⟩
  · rw [hweight]
    exact sq_nonneg _
  · rw [hweight]
    constructor
    · intro hz
      have hdiff : g - h = 0 := sq_eq_zero_iff.mp hz
      constructor <;> omega
    · rintro ⟨rfl, rfl⟩
      simp

/-- The nonnegative exponent used after the Fourier projection. -/
def squareExponent {M : ℕ} (g h : Fin M) : ℕ :=
  Int.toNat (((g.val : ℤ) - h.val) ^ 2)

theorem squareExponent_eq_zero_iff {M : ℕ} (g h : Fin M) :
    squareExponent g h = 0 ↔ g = h := by
  constructor
  · intro he
    have hnonneg : 0 ≤ ((g.val : ℤ) - h.val) ^ 2 := sq_nonneg _
    have hz : ((g.val : ℤ) - h.val) ^ 2 = 0 := by
      unfold squareExponent at he
      omega
    have hdiff : (g.val : ℤ) - h.val = 0 := sq_eq_zero_iff.mp hz
    apply Fin.ext
    omega
  · rintro rfl
    simp [squareExponent]

theorem squareExponent_le {M : ℕ} (g h : Fin M) :
    squareExponent g h ≤ (M - 1) ^ 2 := by
  have hg := g.isLt
  have hh := h.isLt
  have hlow : -((M - 1 : ℕ) : ℤ) ≤ (g.val : ℤ) - h.val := by omega
  have hhigh : (g.val : ℤ) - h.val ≤ ((M - 1 : ℕ) : ℤ) := by omega
  have hprod :
      0 ≤ (((M - 1 : ℕ) : ℤ) - ((g.val : ℤ) - h.val)) *
        (((M - 1 : ℕ) : ℤ) + ((g.val : ℤ) - h.val)) :=
    mul_nonneg (by omega) (by omega)
  have hsq : ((g.val : ℤ) - h.val) ^ 2 ≤ (((M - 1 : ℕ) : ℤ)) ^ 2 := by
    nlinarith
  have hcast : ((g.val : ℤ) - h.val) ^ 2 ≤ (((M - 1) ^ 2 : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow] using hsq
  unfold squareExponent
  omega

end OAI.LinearAlgebra.TensorSpectrum.Separation
