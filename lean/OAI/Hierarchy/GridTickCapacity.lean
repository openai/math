import OAI.Hierarchy.TickResourceBounds
import OAI.Hierarchy.GridTraceCap

namespace OAI
/-! # Capacity of each receiving tick after the factor schedule -/

namespace Hierarchy.GridScale

open Filter FactorAllocation

/-- The common scale provides room at every individual tick for all of its work
and pin advice. The work input is the actual total charge of the trace and the
advice input counts its original external data. A polynomial overhead can be
charged on every unit, including the indivisible-item rounding error. -/
theorem tick_capacity {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    (k A c₁ c₂ C J r : ℕ) (hk : 0<k) (saving : UniversalTick.saving+c₁+(c₂+r)<A)
    {α : Type*} :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w →
    let a := overhead Q D w
    let g := side a
    let B := pairs A w q
    let charge := J*(w+1)^r
    ∀ (cap : ℕ) (_ : (cap:ℝ) ≤ ((2:ℝ)^w)^(3/5:ℝ))
      (cost : α → Fin (k+2) → ℕ) (items : List α) (work advice : Fin (k+2))
      (_ : ∀ z∈items, ∀ j, cost z j ≤ cap)
      (_ : (items.map (fun z => cost z work)).sum ≤ C*2^(evalDepth w k A c₁ a q)*w^c₂)
      (_ : (items.map (fun z => cost z advice)).sum ≤ C*(external k a B+B*w^2))
      (t : Fin (g^k*q)),
      charge*((factors w cost items t).map (fun z => cost z work)).sum ≤ UniversalTick.clock w UniversalTick.saving ∧
      charge*((factors w cost items t).map (fun z => cost z advice)).sum ≤ pins w a := by
  filter_upwards [rounding_room env k A J r UniversalTick.saving,
    average_work env k A c₁ (c₂+r) (4*J*C*2^r) saving,
    controller_room env k A (4*J*C) r hk, eventually_ge_atTop 1] with w rounding workRoom pinRoom hw
  intro q pos top
  dsimp only
  intro cap capSmall cost items work advice bounded workBound adviceBound t
  let a := overhead Q D w
  let B := pairs A w q
  let T := ticks k a q
  let amt := J*(w+1)^r
  have wrap : cap ≤ 2^w := by
    have large : (1:ℝ) ≤ (2:ℝ)^w := one_le_pow₀ (by norm_num)
    have cmp := Real.rpow_le_rpow_of_exponent_le large (by norm_num : (3/5:ℝ)≤1)
    rw [Real.rpow_one] at cmp
    exact_mod_cast capSmall.trans cmp
  have width (z) (hz : z∈items) (j) := (bounded z hz j).trans wrap
  have err := rounding q pos top cap capSmall
  have avgW : 4*amt*(items.map (fun z => cost z work)).sum ≤ T*UniversalTick.clock w UniversalTick.saving := by
    have poly : (w+1)^r ≤ 2^r*w^r := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left (by omega) _
    calc
      _ ≤ 4*(J*(2^r*w^r))*(C*2^(evalDepth w k A c₁ a q)*w^c₂) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ poly)) workBound
      _ = (4*J*C*2^r)*2^(evalDepth w k A c₁ a q)*w^(c₂+r) := by rw [pow_add]; ring
      _ ≤ _ := by simpa only [Nat.mul_comm T] using workRoom q pos top
  have avgP : 4*amt*(items.map (fun z => cost z advice)).sum ≤ T*pins w a := by
    calc
      _ ≤ 4*amt*(C*(external k a B+B*w^2)) := Nat.mul_le_mul_left _ adviceBound
      _ = (4*J*C)*(w+1)^r*(external k a B+B*w^2) := by simp only [amt]; ring
      _ ≤ _ := (pinRoom q pos top).2
  exact ⟨resource_fits cost items work t width bounded avgW err.2,
    resource_fits cost items advice t width bounded avgP err.1⟩

end Hierarchy.GridScale

end OAI
