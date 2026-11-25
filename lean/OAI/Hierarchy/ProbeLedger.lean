import OAI.Hierarchy.ProbePotential

namespace OAI
/-! # The adaptive account under physical inventory and time increments -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {I : Type*} [Fintype I]

/-- The offered price is supported by actual outstanding stock, including on both box faces. -/
theorem offer_stock {a b M s z A : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M) (hs : 0 < s)
    (hz : 0 ≤ z) : s*(2*a*offer a b M s z A) ≤ z := by
  have der := (critical_spec ha hb hM hs hz).2
  have slope := rowSlope_mono (M:=M) ha.le hb (min_le_right A (critical a b M s z))
  have low : 2*a*offer a b M s z A ≤ rowSlope a b M (offer a b M s z A) := by
    dsimp [rowSlope]
    linarith [mul_nonneg (show 0≤2*b by positivity) (rise_nonneg M (offer a b M s z A))]
  exact (mul_le_mul_of_nonneg_left (low.trans slope) hs.le).trans_eq der

private theorem increment_row {a b M s s' z δ x y : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hs' : 0 < s')
    (support : (z-s*rowSlope a b M x)*(y-x)≤0) :
    (z+δ)*y - s'*rowScore a b M y ≤
      z*x-s*rowScore a b M x + δ*x - (s'-s)*rowScore a b M x +
      (δ-(s'-s)*rowSlope a b M x)^2/(4*s'*a) := by
  have rise_pay := mul_nonneg hb (sq_nonneg (rise M y-rise M x))
  have lower := rowDivergence_lower a b M x y hb
  have convex : s'*(a*(y-x)^2) ≤ s'*rowDivergence a b M x y :=
    mul_le_mul_of_nonneg_left (by linarith) hs'.le
  let c := δ-(s'-s)*rowSlope a b M x
  have square := sq_nonneg (c-2*s'*a*(y-x))
  have young : c*(y-x) - s'*a*(y-x)^2 ≤ c^2/(4*s'*a) := by
    apply (le_div_iff₀ (by positivity : 0<4*s'*a)).2
    nlinarith only [square]
  dsimp only [rowDivergence] at convex
  dsimp only [c] at young
  nlinarith only [young,support,convex]

/-- Explicit quadratic error for a simultaneous time and stock update. The numerator uses
the old maximizer coordinate by coordinate and applies also while time decreases. -/
theorem potential_increment {a M s s' : ℝ} (b A z δ : I → ℝ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s) (hs' : 0 < s')
    (hz : ∀ i, 0 ≤ z i) (hz' : ∀ i, 0 ≤ z i+δ i) (hA : ∀ i, 0 ≤ A i) :
    let x := maximizer a M s b A z
    potential a M s' b A (fun i => z i+δ i) ≤ potential a M s b A z +
      pairing δ x - (s'-s)*score a M b x +
      ∑ i, (δ i-(s'-s)*rowSlope a (b i) M (x i))^2/(4*s'*a) := by
  let x := maximizer a M s b A z
  let y := maximizer a M s' b A (fun i => z i+δ i)
  have row (i : I) := increment_row (ha:=ha) (hb:=hb i) (hs':=hs') (δ:=δ i)
    (x:=x i) (y:=y i) (support:=(offer_spec ha (hb i) hM hs (hz i) (hA i)).2 _
      (offer_spec ha (hb i) hM hs' (hz' i) (hA i)).1)
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simpa only [potential,score,pairing,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.mul_sum,x,y] using total

/-- Evaluating at the physical all-core upper-price vector finishes all remaining inventory. -/
theorem finish_at_core {a M s : ℝ} (b A z : I → ℝ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s)
    (hz : ∀ i, 0 ≤ z i) (hA : ∀ i, 0 ≤ A i) :
    pairing z A ≤ potential a M s b A z+s*score a M b A := by
  have eval := maximizes b A z A ha hb hM hs hz hA (fun i => ⟨hA i,le_rfl⟩)
  linarith

/-- The signed account is allowed to be negative. A uniform lower bound suffices to
bound the number of actual strict-saving steps during one phase. -/
theorem saving_step_bound (steps : ℕ) (value : ℕ → ℝ) {floor gain : ℝ}
    (low : floor ≤ value steps) (drop : ∀ i < steps, value (i+1)+gain ≤ value i) :
    steps*gain ≤ value 0-floor := by
  have spent (j : ℕ) (hj : j ≤ steps) : value j+j*gain ≤ value 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have a := ih (by omega)
      have b := drop j (by omega)
      push_cast
      linarith
  linarith [spent steps le_rfl]

end
end Hierarchy.AdaptiveProbe

end OAI
