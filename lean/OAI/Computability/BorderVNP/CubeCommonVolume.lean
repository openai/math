import OAI.Computability.BorderVNP.CubeGroupChargeRoom
import OAI.Computability.BorderVNP.CubePhysicalPaddingPublic

/-! # One physical packet reservation for every terminal history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Finset Filter TeamScales

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [DecidableEq Cell]
    {A : Type*} [Fintype A] {N : Network D P bits} {cell : N.Site → Cell}
    {recv : A → Cell} {dataWidth : A → ℕ} {M Z : ℕ}

/-- Once the balancing inequality holds at a positive volume, it also holds
at a larger volume. Incidence at each actual cell stays bounded by the same M. -/
theorem PackedLabelBudget.enlarge {W X : ℝ} (budget : PackedLabelBudget N cell recv dataWidth W M Z)
    (positive : 0 < W) (room : W ≤ X) : PackedLabelBudget N cell recv dataWidth X M Z := by
  let t := X/W
  have ht : 1 ≤ t := (one_le_div positive).mpr room
  have nonneg : 0 ≤ t := zero_le_one.trans ht
  have eq : t*W = X := div_mul_cancel₀ X positive.ne'
  refine ⟨budget.cableVolume.trans (by gcongr),budget.dataVolume.trans room,
    budget.cableIncidence,budget.dataIncidence,?_⟩
  calc
    _ = t*((Z:ℝ)^2*(4*W*M) + Z*(W*M)) := by rw [← eq]; ring
    _ ≤ t*(W/(Z:ℝ)^2)^2 := mul_le_mul_of_nonneg_left budget.variance nonneg
    _ ≤ t^2*(W/(Z:ℝ)^2)^2 := mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg nonneg (sub_nonneg.mpr ht)]) (sq_nonneg _)
    _ = _ := by rw [← eq,mul_div_assoc,mul_pow]

/-- A common threshold gives the same reservation to every network and every
history at a fixed processor length. The genuine volume and incidence bounds
can come from a smaller initial budget, including an empty network. -/
theorem eventually_common_label_budget {α ξ : ℝ} (hα : 0 < α) (a : ℕ)
    (gap : 24*α*a + 1/4 < 1-ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (r R : ℕ), 1 ≤ r → 1 ≤ R →
      let X := (R*exterior ξ r n : ℕ)
      ∀ {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [DecidableEq Cell]
        {A : Type*} [Fintype A] {N : Network D P bits} {cell : N.Site → Cell}
        {recv : A → Cell} {width : A → ℕ} {M : ℕ} {W : ℝ},
        PackedLabelBudget N cell recv width W M (labelCount α a n) →
        W ≤ X → (M:ℝ) ≤ (n:ℝ)^(1/4:ℝ) →
        PackedLabelBudget N cell recv width X M (labelCount α a n) := by
  have pos : 0 < 1-ξ := (by positivity : 0 < 24*α*a+1/4).trans gap
  filter_upwards [eventually_balancing_slack hα a gap,eventually_exterior_volume_lower pos] with n slack volume
  intro r R hr hR X D P bits Cell eqCell A finiteA N cell recv width M W budget small incidence
  have lower : (n:ℝ)^(1-ξ)/2 ≤ X := by simpa only [X,Nat.mul_comm R] using volume r R hr hR
  exact ⟨budget.cableVolume.trans (by gcongr),budget.dataVolume.trans small,budget.cableIncidence,
    budget.dataIncidence,slack X M lower (Nat.cast_nonneg _) incidence⟩

end Cube.Physical

end BorderVNP
end Computability
end OAI
