import OAI.Optimization.LinearProgramming.PriceGame.Charging

/-! # Median price tests in a failed trial -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

/-- The number of calls in each group is odd. -/
abbrev Calls (k : ℕ) := Fin (2*k+1)

/-- Equal weights on the calls in a group. -/
def uniform (k : ℕ) (_ : Calls k) : ℚ := 1 / (2*k+1)

theorem uniform_nonneg {k : ℕ} (b : Calls k) : 0 ≤ uniform k b := by
  unfold uniform; positivity

theorem uniform_sum (k : ℕ) : ∑ b : Calls k, uniform k b = 1 := by
  simp [uniform, Calls, Nat.cast_add, Nat.cast_mul]
  field_simp

/-- For the positive sign, a price fails below the threshold. For the negative
sign, it fails above the sign-adjusted threshold. Exact equality succeeds. -/
def misses (h : Bool) (threshold price : ℚ) : Bool :=
  if h then decide (price < threshold) else decide (threshold < price)

/-- A strict price failure at the median occurs on more than half the calls. -/
theorem median_miss_majority {k : ℕ} (h : Bool) (t : ℚ) (price : Calls k → ℚ)
    (hm : misses h t (oddMedian price) = true) :
    1/2 ≤ weighted (uniform k) (fun b => if misses h t (price b) then 1 else 0) := by
  apply half_uniform
  cases h with
  | false =>
    have hlt : t < oddMedian price := by simpa [misses] using hm
    apply (card_oddMedian_le price).trans
    apply card_le_card
    intro b hb
    exact mem_filter.mpr ⟨mem_univ _, by simpa [misses] using hlt.trans_le (mem_filter.mp hb).2⟩
  | true =>
    have hlt : oddMedian price < t := by simpa [misses] using hm
    apply (card_le_oddMedian price).trans
    apply card_le_card
    intro b hb
    exact mem_filter.mpr ⟨mem_univ _, by simpa [misses] using ((mem_filter.mp hb).2.trans_lt hlt)⟩

/-- The probe median case of Lemma 6.2 with its actual ordered prices and
positive-surplus vertex masses. -/
theorem median_probe_mass {I : Type*} [Fintype I] {k : ℕ}
    (h : Bool) (t w : I → ℚ) (prices : Calls k → I → ℚ) (hw : ∀ i, 0 ≤ w i) :
    (1/2) * weighted w (fun i => if misses h (t i) (oddMedian fun b => prices b i) then 1 else 0) ≤
      weighted (uniform k) (fun b => weighted w (fun i => if misses h (t i) (prices b i) then 1 else 0)) :=
  median_surplus w (uniform k) (fun b i => misses h (t i) (prices b i))
    (fun i => misses h (t i) (oddMedian fun b => prices b i)) hw uniform_nonneg
    (fun i => median_miss_majority h (t i) (fun b => prices b i))

/-- Failure of the returned coordinatewise median means that at least half the
final calls fail a single parent coordinate. If successful children satisfy all
parent price constraints, at least half the final children must have failed. -/
theorem median_final_failures {I : Type*} {k : ℕ} (h : Bool) (t : I → ℚ)
    (prices : Calls k → I → ℚ) (failed : Calls k → Bool)
    (hret : ∃ i, misses h (t i) (oddMedian fun b => prices b i) = true)
    (hsuccess : ∀ b, failed b = false → ∀ i, misses h (t i) (prices b i) = false) :
    1/2 ≤ weighted (uniform k) (fun b => if failed b then 1 else 0) := by
  obtain ⟨i, hi⟩ := hret
  apply (median_miss_majority h (t i) (fun b => prices b i) hi).trans
  apply sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (uniform_nonneg b)
  dsimp only
  cases hb : failed b with
  | false => simp [hsuccess b hb i]
  | true => cases hm : misses h (t i) (prices b i) <;> norm_num

/-- Total mass of the coordinates with positive surplus. The type `I` indexes
active vertices only; the sign is absorbed in the choice of `misses`. -/
def violatedMass {I : Type*} [Fintype I] (m : I → ℚ) (h : Bool) (t y : I → ℚ) : ℚ :=
  weighted m (fun i => if misses h (t i) (y i) then 1 else 0)

theorem violatedMass_le_total {I : Type*} [Fintype I] (m : I → ℚ) (hm : ∀ i, 0 ≤ m i)
    (h : Bool) (t y : I → ℚ) : violatedMass m h t y ≤ ∑ i, m i := by
  apply sum_le_sum
  intro i _
  dsimp only
  split <;> simp [hm]

/-- Section 6 charge step specialized to the real probe/final price arrays.
A failed inherited final state must occur whenever its mapped prices miss a
parent constraint. Probe gains come from local experts and deep scores from
child calls. Only inequality and mass conditions from the child induction
and feedback are required. -/
theorem failed_price_trial {I E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    {k : ℕ} (d : ℕ) (δ : ℚ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : Bool)
    (mass t : I → ℚ) (probe final : Calls k → I → ℚ)
    (q : E → ℚ) (w : F → ℚ) (g : Calls k → E → ℚ)
    (wc s : Sum (Calls k) (Calls k) → F → ℚ) (pf ff : Calls k → Bool)
    (hm : ∀ i, 0 ≤ mass i) (hM : ∑ i, mass i ≤ 1) (hq : ∀ e, 0 ≤ q e) (hw : ∀ e, 0 ≤ w e)
    (hmLocal : ∑ e, (∑ i, mass i)^d/4*q e ≤ 1) (hmDeep : ∑ e, w e ≤ 1)
    (hret : ∃ i, misses h (t i) (oddMedian fun b => final b i) = true)
    (hfinal : violatedMass mass h t (fun i => oddMedian fun b => probe b i) ≤ δ →
      ∀ b, ff b = false → ∀ i, misses h (t i) (final b i) = false)
    (hpass : ∀ b, pf b = false → violatedMass mass h t (probe b)/2 ≤ weighted q (g b))
    (hbad : ∀ b, pf b = true → -1 ≤ weighted q (g b))
    (hs : ∀ b e, 0 ≤ s b e)
    (hle : ∀ b, Sum.elim pf ff b = true → ∀ e, wc b e ≤ (8/δ^(d+1)) * w e)
    (hchild : ∀ b, Sum.elim pf ff b = true → 1 ≤ weighted (wc b) (s b)) :
    let σ := δ / (32 * (8 / δ^(d+1)))
    1 ≤ weighted (fun e => (∑ i, mass i)^d/4 * q e)
        (fun e => (roundCharge σ (weighted (uniform k) (fun b => g b e)) : ℚ)) +
      weighted w (fun e => (roundCharge σ (weighted (childWeights (uniform k)) (fun b => s b e)) : ℚ)) := by
  apply failed_node_charge d δ (∑ i, mass i) (violatedMass mass h t (fun i => oddMedian fun b => probe b i))
    hδ hδ1 (violatedMass_le_total mass hm h t _) (uniform k) (fun b => violatedMass mass h t (probe b))
    q w g wc s pf ff uniform_nonneg hq hw (sum_nonneg fun i _ => hm i) hmLocal hmDeep
    (fun b => (violatedMass_le_total mass hm h t (probe b)).trans hM) _ _ hpass hbad hs hle hchild
  · intro hlarge
    have hmed := median_probe_mass h t mass probe hm
    calc
      δ/2 ≤ (1/2) * violatedMass mass h t (fun i => oddMedian fun b => probe b i) := by linarith only [hlarge]
      _ ≤ _ := hmed
  · intro hsmall
    exact median_final_failures h t final ff hret (hfinal hsmall)

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
