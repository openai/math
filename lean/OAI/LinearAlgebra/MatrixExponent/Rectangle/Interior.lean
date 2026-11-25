import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior.Convert
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior.Fill
import OAI.LinearAlgebra.MatrixExponent.Rectangle
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding.Swap

section
/-!
# The private-product bound below the harmonic threshold

The square grid and the growth base may depend on the shape and
field. The coefficient in the quadratic saving depends only on the
folding constant and the fixed thin formula.
-/

universe u

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Filter

theorem of_folds {K : ℝ} (hK : 1 ≤ K) (h : Folding.Folds K) :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Type u) [Field F] (x y z : ℝ),
      0 < x → 0 < y → x + y = 1 → 0 ≤ z → z < x * y →
      ∀ᶠ n : ℕ in atTop, ∃ r : ℕ, PrivateProducts F (side n x) (side n y) (side n z) r ∧
        (r : ℝ) ≤ 12 * side n x * side n y * (n : ℝ) ^ (-(c * (x * y - z) ^ 2)) := by
  obtain ⟨S, hS, hs⟩ := thin.{0}
  let a := 1 + (8 * (K + 4) + 1) * S
  have ha : 1 ≤ a := le_add_of_nonneg_right (by positivity)
  let c := 1 / (16 * (4 * a + 1) ^ 2)
  refine ⟨c, by unfold c; positivity, ?_⟩
  intro F _ x y z hx hy hxy hz hgap
  obtain ⟨L, _, ⟨alg⟩⟩ := small_field F
  obtain ⟨q, l, θ, φ, hl, hq, hθ, hφ, hx', hy', hz', hc⟩ := parameters hx hy hxy hz hgap ha
  have hq' : 0 < (q : ℝ) := by rw [hq]; positivity
  have hb : exponent L x y (x * y) < 1 + 1 / (8 * (q : ℝ)) := by
    rw [flat L hx hy (by positivity) (by simp [hxy]), hxy]
    exact lt_add_of_pos_right _ (by positivity)
  obtain ⟨m, d, hm, hr, hd⟩ := (exponent_lt_iff_rank hx.le hy.le (by positivity)).mp hb
  obtain ⟨b, hb, hh⟩ := signals h hK hl hq hm hxy hr hd.le
  have hv : 1 + (8 * (K + 4) * l + 1) * S ≤ a * l := by
    unfold a
    nlinarith only [hl, mul_le_mul_of_nonneg_right hl (show (0 : ℝ) ≤ S by positivity)]
  apply fill hb hθ hφ (by positivity) (by positivity) (by positivity) hx' hy' hz' hc
  filter_upwards [hh, (tendsto_pow_atTop_atTop_of_one_lt hb).eventually_ge_atTop 2] with n hn ht
  obtain ⟨v⟩ := hn
  obtain ⟨i, j, k, r, hi, hj, hI, hJ, hZ, hR, hpr⟩ := v.convert ht (by nlinarith) hS
    (Nat.lt_pow_self (by decide : 1 < 2)).le (hs L)
  refine ⟨i, j, k, r, hi, hj, hI.trans ?_, hJ.trans ?_, hZ, hR, hpr.map (algebraMap L F)⟩ <;>
    apply Real.rpow_le_rpow_of_exponent_le (by linarith) <;> linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

section
/-! # One private product per output strictly below the harmonic threshold -/

universe u

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter Interior

/-- The positive constant in the quadratic saving is absolute. The
size from which the bound holds may depend on the field and shape. -/
theorem private_products :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Type u) [Field F] (x y z : ℝ),
      0 < x → 0 < y → x + y = 1 → 0 ≤ z → z < x * y →
      ∀ᶠ n : ℕ in atTop, ∃ r : ℕ,
        PrivateProducts F (side n x) (side n y) (side n z) r ∧
        RankLE F (side n x) (side n y) (side n z) (side n x * side n y + r) ∧
        (r : ℝ) ≤ 12 * side n x * side n y * (n : ℝ) ^ (-(c * (x * y - z) ^ 2)) := by
  obtain ⟨c, hc, h⟩ := of_folds.{u} Folding.one_le_coefficient (Folding.of_swap Folding.swap_bound)
  refine ⟨c, hc, fun F _ x y z hx hy he hz hz' => ?_⟩
  filter_upwards [h F x y z hx hy he hz hz'] with n hn
  obtain ⟨r, hr, hbound⟩ := hn
  exact ⟨r, hr, hr.rank, hbound⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
