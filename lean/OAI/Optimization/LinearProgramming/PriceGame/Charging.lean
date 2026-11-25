import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! # Charging a failed price-game trial

The score returned by a trial is computed from a rational average and rounded up.
The estimates below count probe mass and expert mass separately. This allows the
same fixed collection of experts to be used at all probes, even though a child
may have several admissible states.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging

open Finset

/-- Finite expectation with possibly unnormalized weights. -/
def weighted {I : Type*} [Fintype I] (w f : I → ℚ) : ℚ := ∑ i, w i * f i

private theorem weighted_mono {I : Type*} [Fintype I] {w f g : I → ℚ}
    (hw : ∀ i, 0 ≤ w i) (hfg : ∀ i, f i ≤ g i) : weighted w f ≤ weighted w g :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfg i) (hw i)

private theorem weighted_const {I : Type*} [Fintype I] (w : I → ℚ) (c : ℚ) :
    weighted w (fun _ => c) = (∑ i, w i) * c := by
  simp [weighted, sum_mul]

private theorem weighted_add {I : Type*} [Fintype I] (w f g : I → ℚ) :
    weighted w (fun i => f i + g i) = weighted w f + weighted w g := by
  simp [weighted, mul_add, sum_add_distrib]

private theorem weighted_sub {I : Type*} [Fintype I] (w f g : I → ℚ) :
    weighted w (fun i => f i - g i) = weighted w f - weighted w g := by
  simp [weighted, mul_sub, sum_sub_distrib]

private theorem weighted_smul {I : Type*} [Fintype I] (w f : I → ℚ) (c : ℚ) :
    weighted w (fun i => c * f i) = c * weighted w f := by
  simp [weighted, mul_sum, mul_left_comm]

/-- Average over probes and then experts, or over experts and then probes. -/
theorem weighted_swap {I J : Type*} [Fintype I] [Fintype J] (w : I → ℚ) (v : J → ℚ)
    (f : I → J → ℚ) :
    weighted w (fun i => weighted v (f i)) = weighted v (fun j => weighted w (fun i => f i j)) := by
  simp only [weighted, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- The score formula, with `C = 2/σ`. The output is a nonnegative integer. -/
def roundCharge (σ v : ℚ) : ℕ := ⌈(2 / σ) * max 0 (v - σ / 2)⌉₊

/-- The rounding step turns mean gain `σ` into at least one unit of score,
including when the total weight of the expert group is less than one. -/
theorem roundCharge_weighted {I : Type*} [Fintype I] {σ : ℚ} (hσ : 0 < σ)
    (w H : I → ℚ) (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i ≤ 1)
    (hgain : σ ≤ weighted w H) : 1 ≤ weighted w (fun i => (roundCharge σ (H i) : ℚ)) := by
  have hp (i : I) : H i ≤ σ / 2 + σ / 2 * (roundCharge σ (H i) : ℚ) := by
    have hceil := Nat.le_ceil ((2 / σ) * max 0 (H i - σ / 2))
    have h : (2 / σ) * (H i - σ / 2) ≤ (roundCharge σ (H i) : ℚ) :=
      (mul_le_mul_of_nonneg_left (le_max_right 0 _) (by positivity)).trans hceil
    have hs := mul_le_mul_of_nonneg_left h hσ.le
    field_simp [ne_of_gt hσ] at hs
    linarith
  have hsum := hgain.trans (weighted_mono hw hp)
  rw [weighted_add, weighted_const, weighted_smul] at hsum
  have hmass' := mul_le_mul_of_nonneg_right hmass (show 0 ≤ σ/2 by positivity)
  by_contra! h
  have hh := mul_lt_mul_of_pos_left h (show 0 < σ/2 by positivity)
  linarith

/-- Transfer the child induction hypothesis to the parent's fixed weights. -/
theorem charge_transfer {I : Type*} [Fintype I] {C : ℚ} (hC : 0 < C)
    (w w' s : I → ℚ) (hs : ∀ i, 0 ≤ s i) (hle : ∀ i, w' i ≤ C * w i)
    (hc : 1 ≤ weighted w' s) : 1 / C ≤ weighted w s := by
  apply (div_le_iff₀ hC).2
  calc
    (1 : ℚ) ≤ weighted w' s := hc
    _ ≤ ∑ i, (C * w i) * s i := sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hle i) (hs i)
    _ = weighted w s * C := by simp [weighted, sum_mul]; ring_nf

/-- Local probes may fail, in which case the only available gain bound is `-1`.
The loss relative to `v/2` is at most `3/2` per failed probe. -/
theorem expected_probe_gain {I : Type*} [Fintype I] (δ : ℚ)
    (p v g : I → ℚ) (fails : I → Bool) (hp : ∀ i, 0 ≤ p i)
    (hv : ∀ i, v i ≤ 1) (hpass : ∀ i, fails i = false → v i / 2 ≤ g i)
    (hfail : ∀ i, fails i = true → -1 ≤ g i)
    (hmass : δ / 2 ≤ weighted p v)
    (hcount : weighted p (fun i => if fails i then 1 else 0) ≤ δ / 16) :
    δ / 8 ≤ weighted p g := by
  have h : ∀ i, (1/2 : ℚ) * v i - (3/2 : ℚ) * (if fails i then 1 else 0) ≤ g i := by
    intro i
    cases hi : fails i with
    | false => simpa [hi, div_eq_mul_inv, mul_comm] using hpass i hi
    | true => simp only [↓reduceIte, mul_one]; linarith [hfail i hi, hv i]
  have h' := weighted_mono hp h
  rw [weighted_sub, weighted_smul, weighted_smul] at h'
  have hδ : 0 ≤ δ := by
    have hnon : 0 ≤ weighted p (fun i => if fails i then 1 else 0) :=
      sum_nonneg fun i _ => mul_nonneg (hp i) (by dsimp only; split <;> norm_num)
    linarith
  linarith

/-- Local expert weights multiply the tuple distribution by `M^d/4`.
The paper fixes `σ = δ/(32 * (8/δ^(d+1)))`. -/
theorem local_charge_threshold {δ M g : ℚ} (d : ℕ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : δ ≤ M) (hg : δ/8 ≤ g) :
    δ / (32 * (8 / δ^(d+1))) ≤ M^d / 4 * g := by
  have hp := pow_le_pow_left₀ hδ.le hM d
  have hfirst : δ / (32 * (8 / δ^(d+1))) ≤ δ^(d+1) / 32 := by
    have hd : 0 < δ^(d+1) := pow_pos hδ _
    field_simp [ne_of_gt hd]
    nlinarith [mul_le_mul_of_nonneg_right hδ1 hd.le]
  calc
    _ ≤ δ^(d+1) / 32 := hfirst
    _ = δ^d/4 * (δ/8) := by rw [pow_succ]; ring
    _ ≤ M^d/4 * g := mul_le_mul (by linarith) hg (by positivity) (by have := hδ.le.trans hM; positivity)

/-- Finite averaging of the induction hypothesis when a child has several
possible states. A state of weight zero imposes no constraint. -/
theorem charge_mixture {I J : Type*} [Fintype I] [Fintype J]
    (p : J → ℚ) (wc : J → I → ℚ) (s : I → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hnorm : ∑ j, p j = 1) (hchild : ∀ j, 0 < p j → 1 ≤ weighted (wc j) s) :
    1 ≤ weighted (fun i => weighted p (fun j => wc j i)) s := by
  have hswap : weighted (fun i => weighted p (fun j => wc j i)) s =
      weighted p (fun j => weighted (wc j) s) := by
    simp only [weighted, sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => mul_assoc _ _ _
  rw [hswap]
  calc
    1 = ∑ j, p j := hnorm.symm
    _ ≤ weighted p (fun j => weighted (wc j) s) := by
      apply sum_le_sum
      intro j _
      rcases (hp j).eq_or_lt with hj | hj
      · simp [← hj]
      · simpa using mul_le_mul_of_nonneg_left (hchild j hj) (hp j)

/-- If a `δ/32` fraction of all calls fail in every state in their mixture,
then the deep experts reach the group threshold `δ/(32 C)`. The `wc` parent
comparison and child charge can use different mixtures for each call. -/
theorem deeper_charge_threshold {E B : Type*} [Fintype E] [Fintype B]
    (C δ : ℚ) (hC : 0 < C) (w : E → ℚ) (p : B → ℚ) (wc s : B → E → ℚ)
    (failed : B → Bool) (hp : ∀ b, 0 ≤ p b) (hw : ∀ e, 0 ≤ w e)
    (hs : ∀ b e, 0 ≤ s b e)
    (hle : ∀ b, failed b = true → ∀ e, wc b e ≤ C * w e)
    (hchild : ∀ b, failed b = true → 1 ≤ weighted (wc b) (s b))
    (hmany : δ/32 ≤ weighted p (fun b => if failed b then 1 else 0)) :
    δ/(32*C) ≤ weighted w (fun e => weighted p (fun b => s b e)) := by
  have hpoint (b : B) : (1/C) * (if failed b then 1 else 0) ≤ weighted w (s b) := by
    cases hb : failed b with
    | false => simpa [weighted] using (sum_nonneg fun e (_ : e ∈ (univ : Finset E)) => mul_nonneg (hw e) (hs b e))
    | true => simpa using charge_transfer hC w (wc b) (s b) (hs b) (hle b hb) (hchild b hb)
  have h := weighted_mono hp hpoint
  rw [weighted_smul, weighted_swap p w s] at h
  calc
    _ = (1/C) * (δ/32) := by ring
    _ ≤ (1/C) * weighted p (fun b => if failed b then 1 else 0) :=
      mul_le_mul_of_nonneg_left hmany (by positivity)
    _ ≤ _ := h

/-- The fixed distribution of local tuple experts is used in every probe. -/
theorem local_charge_from_probes {E B : Type*} [Fintype E] [Fintype B]
    (d : ℕ) (δ M : ℚ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : δ ≤ M)
    (q : E → ℚ) (p v : B → ℚ) (g : B → E → ℚ) (fails : B → Bool)
    (hp : ∀ b, 0 ≤ p b) (hv : ∀ b, v b ≤ 1)
    (hpass : ∀ b, fails b = false → v b/2 ≤ weighted q (g b))
    (hfail : ∀ b, fails b = true → -1 ≤ weighted q (g b))
    (hmass : δ/2 ≤ weighted p v)
    (hcount : weighted p (fun b => if fails b then 1 else 0) ≤ δ/16) :
    δ / (32 * (8 / δ^(d+1))) ≤
      weighted (fun e => (M^d/4) * q e) (fun e => weighted p (fun b => g b e)) := by
  have h := local_charge_threshold d hδ hδ1 hM
    (expected_probe_gain δ p v (fun b => weighted q (g b)) fails hp hv hpass hfail hmass hcount)
  rw [weighted_swap p q g] at h
  convert h using 1
  simp [weighted, mul_sum, mul_assoc]

/-- Positive surplus at the coordinatewise median forces at least half as much
positive-surplus mass on average across the probes. -/
theorem median_surplus {I B : Type*} [Fintype I] [Fintype B]
    (w : I → ℚ) (p : B → ℚ) (probe : B → I → Bool) (median : I → Bool)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ b, 0 ≤ p b)
    (hmedian : ∀ i, median i = true → 1/2 ≤ weighted p (fun b => if probe b i then 1 else 0)) :
    (1/2) * weighted w (fun i => if median i then 1 else 0) ≤
      weighted p (fun b => weighted w (fun i => if probe b i then 1 else 0)) := by
  rw [weighted_swap p w (fun b i => if probe b i then 1 else 0), ← weighted_smul]
  apply weighted_mono hw
  intro i
  cases hi : median i with
  | true => simpa using hmedian i hi
  | false =>
    have hnon : 0 ≤ weighted p (fun b => if probe b i then 1 else 0) :=
      sum_nonneg fun b _ => mul_nonneg (hp b) (by dsimp only; split <;> norm_num)
    simpa using hnon

/-- The middle price, with ties retained, of an odd list of prices. -/
def oddMedian {α : Type*} [LinearOrder α] {k : ℕ} (f : Fin (2*k+1) → α) : α :=
  f (Tuple.sort f ⟨k, by omega⟩)

/-- More than half of the original entries lie weakly below the median. -/
theorem card_le_oddMedian {α : Type*} [LinearOrder α] {k : ℕ} (f : Fin (2*k+1) → α) :
    k + 1 ≤ (univ.filter fun i => f i ≤ oddMedian f).card := by
  let middle : Fin (2*k+1) := ⟨k, by omega⟩
  calc
    k+1 = (Iic middle).card := by simp [Fin.card_Iic, middle]
    _ = ((Iic middle).map (Tuple.sort f).toEmbedding).card := by simp
    _ ≤ _ := by
      apply card_le_card
      intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
      exact mem_filter.mpr ⟨mem_univ _, Tuple.monotone_sort f (mem_Iic.mp hj)⟩

/-- More than half of the original entries lie weakly above the median. -/
theorem card_oddMedian_le {α : Type*} [LinearOrder α] {k : ℕ} (f : Fin (2*k+1) → α) :
    k + 1 ≤ (univ.filter fun i => oddMedian f ≤ f i).card := by
  let middle : Fin (2*k+1) := ⟨k, by omega⟩
  calc
    k+1 = (Ici middle).card := by rw [Fin.card_Ici]; change k+1 = 2*k+1-k; omega
    _ = ((Ici middle).map (Tuple.sort f).toEmbedding).card := by simp
    _ ≤ _ := by
      apply card_le_card
      intro i hi
      obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
      exact mem_filter.mpr ⟨mem_univ _, Tuple.monotone_sort f (mem_Ici.mp hj)⟩

/-- With an odd number of equally weighted calls, a set containing at least
`k+1` indices has weight at least one half. -/
theorem half_uniform {k : ℕ} (test : Fin (2*k+1) → Bool)
    (h : k+1 ≤ (univ.filter fun i => test i = true).card) :
    1/2 ≤ weighted (fun _ : Fin (2*k+1) => (1 : ℚ)/(2*k+1))
      (fun i => if test i then 1 else 0) := by
  have h' : (k : ℚ)+1 ≤ ((univ.filter fun i => test i = true).card : ℚ) := by exact_mod_cast h
  simp only [weighted, mul_ite, mul_one, mul_zero, ← sum_filter, sum_const, nsmul_eq_mul]
  have hden : 0 < (2*(k : ℚ)+1) := by positivity
  rw [mul_one_div, le_div_iff₀ hden]
  linarith

/-- Each of the two groups of equally many child calls receives half the
mass. The left group represents probe calls and the right group final calls. -/
def childWeights {J : Type*} (p : J → ℚ) : Sum J J → ℚ :=
  Sum.elim (fun j => p j / 2) (fun j => p j / 2)

theorem weighted_children {J : Type*} [Fintype J] (p : J → ℚ) (f : Sum J J → ℚ) :
    weighted (childWeights p) f =
      (weighted p (fun j => f (.inl j)) + weighted p (fun j => f (.inr j))) / 2 := by
  simp only [weighted, Fintype.sum_sum_type, childWeights, Sum.elim_inl, Sum.elim_inr]
  simp only [div_eq_mul_inv, add_mul, sum_mul]; congr 1 <;>
    exact sum_congr rfl fun j _ => by ring

private theorem small_failure_fraction {a b δ : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hδ : δ ≤ 1) (h : (a+b)/2 < δ/32) : a ≤ δ/16 ∧ b < 1/2 := by
  constructor <;> linarith

/-- The failed-node step of Lemma 6.2. `probeFail` and `finalFail` flag calls
failing all child states used at that call. `wc` may therefore be the average
child weights from `charge_mixture`. The two median consequences concern the
median of probe prices and that of the final returned prices, respectively.
The local hypotheses are the expectation bounds on the fixed tuple population. -/
theorem failed_node_charge {E F B : Type*} [Fintype E] [Fintype F] [Fintype B]
    (d : ℕ) (δ M med : ℚ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hmedM : med ≤ M)
    (p v : B → ℚ) (q : E → ℚ) (w : F → ℚ) (g : B → E → ℚ) (wc s : Sum B B → F → ℚ)
    (probeFail finalFail : B → Bool)
    (hp : ∀ b, 0 ≤ p b) (hq : ∀ e, 0 ≤ q e) (hw : ∀ e, 0 ≤ w e)
    (hM : 0 ≤ M) (hmLocal : ∑ e, M^d/4 * q e ≤ 1) (hmDeep : ∑ e, w e ≤ 1)
    (hv : ∀ b, v b ≤ 1)
    (hmedLarge : δ < med → δ/2 ≤ weighted p v)
    (hmedSmall : med ≤ δ → 1/2 ≤ weighted p (fun b => if finalFail b then 1 else 0))
    (hpass : ∀ b, probeFail b = false → v b/2 ≤ weighted q (g b))
    (hfail : ∀ b, probeFail b = true → -1 ≤ weighted q (g b))
    (hs : ∀ b e, 0 ≤ s b e)
    (hle : ∀ b, (Sum.elim probeFail finalFail) b = true → ∀ e, wc b e ≤ (8/δ^(d+1)) * w e)
    (hchild : ∀ b, (Sum.elim probeFail finalFail) b = true → 1 ≤ weighted (wc b) (s b)) :
    let σ := δ / (32 * (8 / δ^(d+1)))
    1 ≤ weighted (fun e => M^d/4 * q e) (fun e => (roundCharge σ (weighted p (fun b => g b e)) : ℚ))
      + weighted w (fun e => (roundCharge σ (weighted (childWeights p) (fun b => s b e)) : ℚ)) := by
  dsimp only
  let σ := δ / (32 * (8 / δ^(d+1)))
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have wloc (e : E) : 0 ≤ M^d/4*q e := mul_nonneg (by positivity) (hq e)
  have wl0 : 0 ≤ weighted (fun e => M^d/4*q e) (fun e => (roundCharge σ (weighted p (fun b => g b e)) : ℚ)) :=
    sum_nonneg fun e _ => mul_nonneg (wloc e) (by positivity)
  have wd0 : 0 ≤ weighted w (fun e => (roundCharge σ (weighted (childWeights p) (fun b => s b e)) : ℚ)) :=
    sum_nonneg fun e _ => mul_nonneg (hw e) (by positivity)
  by_cases hmany : δ/32 ≤ weighted (childWeights p) (fun b => if Sum.elim probeFail finalFail b then 1 else 0)
  · have hc (b : Sum B B) : 0 ≤ childWeights p b := by cases b <;> exact div_nonneg (hp _) (by norm_num)
    have hgate := deeper_charge_threshold (8/δ^(d+1)) δ (by positivity) w (childWeights p) wc s
      (Sum.elim probeFail finalFail) hc hw hs hle hchild hmany
    exact le_add_of_nonneg_of_le wl0 (roundCharge_weighted hσ _ _ hw hmDeep hgate)
  · have hboth := lt_of_not_ge hmany
    rw [weighted_children] at hboth
    simp only [Sum.elim_inl, Sum.elim_inr] at hboth
    have noneg (f : B → Bool) : 0 ≤ weighted p (fun b => if f b then 1 else 0) :=
      sum_nonneg fun b _ => mul_nonneg (hp b) (by dsimp only; split <;> norm_num)
    obtain ⟨hcount, hfew⟩ := small_failure_fraction (noneg probeFail) (noneg finalFail) hδ1 hboth
    have hlarge : δ < med := lt_of_not_ge fun hsmall => (not_le_of_gt hfew) (hmedSmall hsmall)
    have hgate := local_charge_from_probes d δ M hδ hδ1 (hlarge.le.trans hmedM) q p v g probeFail hp
      hv hpass hfail (hmedLarge hlarge) hcount
    exact le_add_of_le_of_nonneg (roundCharge_weighted hσ _ _ wloc hmLocal hgate) wd0

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
