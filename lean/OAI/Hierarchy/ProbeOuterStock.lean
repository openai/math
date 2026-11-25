import OAI.Hierarchy.ProbeStockCap
import OAI.Hierarchy.ProbeFeed

namespace OAI
/-! # Exact integer stock caps in the outer price account -/

namespace Hierarchy.AdaptiveProbe

open scoped BigOperators
noncomputable section

variable {I : Type*}

/-- Real stock units of a bank of integer bit counts at width `w`. -/
def bitStock (w : ℕ) (bits : I → ℕ) (i : I) : ℝ := (bits i : ℝ)/w

def clipBits (B w : ℕ) (bits : I → ℕ) (i : I) : ℕ := min (bits i) (B*w)

def spillBits (B w : ℕ) (bits : I → ℕ) (i : I) : ℕ := bits i - clipBits B w bits i

theorem retained_add_spill (B w : ℕ) (bits : I → ℕ) (i : I) :
    clipBits B w bits i + spillBits B w bits i = bits i :=
  Nat.add_sub_of_le (min_le_left _ _)

theorem bitStock_clip {w : ℕ} (hw : 0<w) (B : ℕ) (bits : I → ℕ) (i : I) :
    bitStock w (clipBits B w bits) i = min (bitStock w bits i) B := by
  have pos : 0<(w:ℝ) := by exact_mod_cast hw
  unfold bitStock clipBits
  by_cases h : bits i ≤ B*w
  · rw [min_eq_left h, min_eq_left ((div_le_iff₀ pos).mpr (by exact_mod_cast h))]
  · have le : B*w ≤ bits i := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right le,min_eq_right ((le_div_iff₀ pos).mpr (by exact_mod_cast le)), Nat.cast_mul]
    field_simp

theorem bitStock_spill (w B : ℕ) (bits : I → ℕ) (i : I) :
    bitStock w (spillBits B w bits) i = bitStock w bits i - bitStock w (clipBits B w bits) i := by
  unfold bitStock spillBits
  rw [Nat.cast_sub (show clipBits B w bits i≤bits i from min_le_left ..), sub_div]

variable [Fintype I]

/-- The numerator of the core-route payment is exactly the sum of the
individual bit prices. -/
theorem spill_payment (B w : ℕ) (bits : I → ℕ) (A : I → ℝ) :
    pairing (bitStock w (spillBits B w bits)) A =
      (∑ i, (spillBits B w bits i : ℝ)*A i)/w := by
  unfold pairing bitStock
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- After a stock increase, each surplus bit pays its core-route price divided by
width. This transfer leaves the unnormalized paid-plus-potential account unchanged. -/
theorem outer_stock_cap {a M s paid : ℝ} {w : ℕ} (B : ℕ) (b A : I → ℝ) (bits : I → ℕ)
    (hw : 0<w) (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s)
    (cap : ∀ i, s*rowSlope a (b i) M (A i) ≤ B) :
    paid + potential a M s b A (bitStock w bits) =
      (paid + pairing (bitStock w (spillBits B w bits)) A) +
        potential a M s b A (bitStock w (clipBits B w bits)) := by
  have znon (i : I) : 0 ≤ bitStock w bits i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have H := potential_stock_cap b A (bitStock w bits) (fun _ => (B:ℝ)) ha hb hM hs znon
    (fun _ => Nat.cast_nonneg _) cap
  dsimp only at H
  simp only [← bitStock_clip hw B bits, ← bitStock_spill w B bits] at H
  linarith only [H]

/-- A realized core route whose charge is bounded by the spilled bits' price
can only reduce the account. -/
theorem outer_stock_cap_paid_le {a M s paid charge : ℝ} {w : ℕ} (B : ℕ) (b A : I → ℝ) (bits : I → ℕ)
    (hw : 0<w) (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s)
    (cap : ∀ i, s*rowSlope a (b i) M (A i) ≤ B)
    (route : charge ≤ pairing (bitStock w (spillBits B w bits)) A) :
    (paid+charge) + potential a M s b A (bitStock w (clipBits B w bits)) ≤
      paid + potential a M s b A (bitStock w bits) := by
  rw [outer_stock_cap B b A bits hw ha hb hM hs cap]
  linarith only [route]

omit [Fintype I] in
/-- Exact integer conservation over all rounded feeds, with the pointwise error
in stock units. Each later cap pays precisely the bits recorded as spills. -/
theorem outer_feed_conservation {w m : ℕ} (hw : 0<w) (hm : 0<m) (B : ℕ)
    (total : I → ℕ) (inventory : ℕ → I → ℕ)
    (update : ∀ j<m, ∀ i, inventory (j+1) i =
      clipBits B w (fun k => inventory j k + slice m (total k) j) i) (i : I) :
    inventory m i + ∑ j ∈ Finset.range m, spillBits B w (fun k => inventory j k + slice m (total k) j) i =
      inventory 0 i + total i ∧
    ∀ j, |bitStock w (fun k => slice m (total k) j) i - bitStock w total i/m| < 1/(w:ℝ) := by
  have account (k : ℕ) (hk : k≤m) :
      inventory k i + ∑ j ∈ Finset.range k, spillBits B w (fun t => inventory j t + slice m (total t) j) i =
        inventory 0 i + ∑ j ∈ Finset.range k, slice m (total i) j := by
    induction k with
    | zero => simp
    | succ k ih =>
      have H := retained_add_spill B w (fun t => inventory k t + slice m (total t) k) i
      rw [← update k (by omega) i] at H
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have prev := ih (by omega)
      omega
  refine ⟨by simpa only [slice_sum _ _ hm] using account m le_rfl,?_⟩
  intro j
  have wp : (0:ℝ)<w := by exact_mod_cast hw
  change |(slice m (total i) j : ℝ)/w - ((total i : ℝ)/w)/m| < _
  rw [show ((total i : ℝ)/w)/m = ((total i : ℝ)/m)/w by ring, ← sub_div, abs_div,
    abs_of_pos wp]
  exact div_lt_div_of_pos_right (slice_error m (total i) j hm) wp

omit [Fintype I] in
/-- A compact box with uniform coefficient and endpoint bounds supplies one
integer slope bound at every position and every outer time `s≤1`. -/
theorem outer_box_cap {a M s bmax amax : ℝ} (b A : I → ℝ)
    (ha : 0≤a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hA : ∀ i, 0≤A i)
    (hbmax : ∀ i, b i≤bmax) (hAmax : ∀ i, A i≤amax) (time : s≤1) (i : I) :
    s*rowSlope a (b i) M (A i) ≤ (⌈2*(a+bmax)*amax⌉₊ : ℝ) := by
  have riseLe : rise M (A i) ≤ amax :=
    max_le (by linarith [hAmax i]) ((hA i).trans (hAmax i))
  have pos : 0≤rowSlope a (b i) M (A i) := by
    unfold rowSlope
    exact add_nonneg (mul_nonneg (by positivity) (hA i))
      (mul_nonneg (mul_nonneg (by norm_num) (hb i)) (rise_nonneg _ _))
  calc
    _ ≤ 1*rowSlope a (b i) M (A i) := mul_le_mul_of_nonneg_right time pos
    _ ≤ 2*(a+bmax)*amax := by
      have first := mul_le_mul_of_nonneg_left (hAmax i) ha
      have second := mul_le_mul (hbmax i) riseLe (rise_nonneg M _) ((hb i).trans (hbmax i))
      dsimp [rowSlope]
      linarith
    _ ≤ _ := Nat.le_ceil _

/-- Crude uniform gradient bounds used by the outer time increment and the
integer reserve-feed estimate. The same natural `B` bounds every coordinate. -/
theorem outer_gradient_box {a M s : ℝ} (b A z : I → ℝ) (B : ℕ)
    (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s) (hz : ∀ i, 0≤z i)
    (hA : ∀ i, 0≤A i) (bound : ∀ i, rowSlope a (b i) M (A i) ≤ B) :
    (∀ i, maximizer a M s b A z i ∈ Set.Icc 0 (A i)) ∧
    (∀ i, |rowSlope a (b i) M (maximizer a M s b A z i)| ≤ B) ∧
    ∑ i, (rowSlope a (b i) M (maximizer a M s b A z i))^2 ≤ (B:ℝ)^2*Fintype.card I := by
  let x := maximizer a M s b A z
  have box (i : I) : x i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM hs (hz i) (hA i)).1
  have lower (i : I) : 0 ≤ rowSlope a (b i) M (x i) := by
    unfold rowSlope
    exact add_nonneg (mul_nonneg (by positivity) (box i).1)
      (mul_nonneg (mul_nonneg (by norm_num) (hb i)) (rise_nonneg _ _))
  have upper (i : I) : rowSlope a (b i) M (x i) ≤ B :=
    (rowSlope_mono ha.le (hb i) (box i).2).trans (bound i)
  refine ⟨box,fun i => (abs_of_nonneg (lower i)).le.trans (upper i),?_⟩
  calc
    _ ≤ ∑ _ : I, (B:ℝ)^2 := Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (lower i) (upper i) _
    _ = _ := by simp [nsmul_eq_mul,mul_comm]

/-- Starting from any capped inventory, the unnormalized potential fits a
linear site budget determined only by the two box bounds and the commodity count. -/
theorem outer_potential_box {a M s n C amax : ℝ} (hmax : 0≤amax) {w : ℕ} (hw : 0<w)
    (B : ℕ) (b A : I → ℝ) (bits : I → ℕ)
    (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s)
    (hA : ∀ i, 0≤A i) (abox : ∀ i, A i≤amax) (count : (Fintype.card I : ℝ)≤C*n) :
    potential a M s b A (bitStock w (clipBits B w bits)) ≤ ((B:ℝ)*amax*C)*n := by
  let z := bitStock w (clipBits B w bits)
  let x := maximizer a M s b A z
  have nz (i : I) : 0≤z i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have zbox (i : I) : z i≤B := (bitStock_clip hw B bits i).le.trans (min_le_right ..)
  have xBox (i : I) : x i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM hs (nz i) (hA i)).1
  have sc : 0 ≤ score a M b x := Finset.sum_nonneg fun i _ =>
    add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg (hb i) (sq_nonneg _))
  change pairing z x - s*score a M b x ≤ _
  calc
    _ ≤ ∑ i, z i*x i := sub_le_self _ (mul_nonneg hs.le sc)
    _ ≤ ∑ _ : I, (B:ℝ)*amax := Finset.sum_le_sum (fun i _ =>
      mul_le_mul (zbox i) ((xBox i).2.trans (abox i)) (xBox i).1 (Nat.cast_nonneg B))
    _ = (B:ℝ)*amax*Fintype.card I := by simp [nsmul_eq_mul,mul_comm]
    _ ≤ (B:ℝ)*amax*(C*n) := mul_le_mul_of_nonneg_left count (mul_nonneg (Nat.cast_nonneg _) hmax)
    _ = _ := (mul_assoc ..).symm

/-- The quadratic gradient budget is linear in the number `n` of sites when the
commodity count is at most `C*n`. -/
theorem outer_gradient_scaled {a M s n C : ℝ} (b A z : I → ℝ) (B : ℕ)
    (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M) (hs : 0<s) (hz : ∀ i, 0≤z i)
    (hA : ∀ i, 0≤A i) (bound : ∀ i, rowSlope a (b i) M (A i) ≤ B)
    (count : (Fintype.card I : ℝ) ≤ C*n) :
    ∑ i, (rowSlope a (b i) M (maximizer a M s b A z i))^2 ≤ ((B:ℝ)^2*C)*n := by
  exact ((outer_gradient_box b A z B ha hb hM hs hz hA bound).2.2.trans
    (mul_le_mul_of_nonneg_left count (sq_nonneg _))).trans_eq (mul_assoc ..).symm

end
end Hierarchy.AdaptiveProbe

end OAI
