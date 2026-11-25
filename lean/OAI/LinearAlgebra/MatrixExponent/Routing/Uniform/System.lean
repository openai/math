import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import OAI.LinearAlgebra.MatrixExponent.Prices.Space
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Perm
import OAI.LinearAlgebra.MatrixExponent.Routing.Partitions
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fintype

/-!
# Paying for outstanding requests

Stock is measured in raw bits, with the batch scale absorbed into the
smoothing parameter. The potential is the maximum linear valuation
minus a quadratic penalty under a separate price cap for each type.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

def price (μ a z : ℝ) : ℝ := min a (z / μ)

def value (μ a z : ℝ) : ℝ := z * price μ a z - μ * (price μ a z) ^ 2 / 2

section Scalar

variable {μ a y z : ℝ}

theorem price_nonneg (hμ : 0 < μ) (ha : 0 ≤ a) (hz : 0 ≤ z) :
    0 ≤ price μ a z := le_min ha (div_nonneg hz hμ.le)

theorem price_le : price μ a z ≤ a := min_le_left _ _

theorem mul_price_le (hμ : 0 < μ) : μ * price μ a z ≤ z := by
  rw [mul_comm]
  exact (le_div_iff₀ hμ).mp (min_le_right _ _)

/-- The first-order condition remains valid when the cap binds. -/
private theorem first_order (hμ : 0 < μ) {b : ℝ} (hb : b ≤ a) :
    (b - price μ a z) * (z - μ * price μ a z) ≤ 0 := by
  rcases le_total a (z / μ) with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (by rw [price, min_eq_left h]; exact hb))
      (sub_nonneg.mpr (mul_price_le hμ))
  · rw [price, min_eq_right h, mul_div_cancel₀ _ hμ.ne', sub_self, mul_zero]

private theorem value_optimal (hμ : 0 < μ) {b : ℝ} (hb : b ≤ a) :
    z * b - μ * b ^ 2 / 2 ≤ value μ a z := by
  unfold value
  nlinarith only [first_order (z := z) hμ hb, mul_nonneg hμ.le (sq_nonneg (b - price μ a z))]

theorem value_nonneg (hμ : 0 < μ) (ha : 0 ≤ a) :
    0 ≤ value μ a z := by simpa using value_optimal (z := z) hμ ha

theorem value_zero (ha : 0 ≤ a) : value μ a 0 = 0 := by
  simp [value, price, ha]

theorem value_close (hμ : 0 < μ) : a * z ≤ value μ a z + μ * a ^ 2 / 2 := by
  linarith only [value_optimal (z := z) hμ (le_refl a)]

theorem value_increment (hμ : 0 < μ) :
    value μ a y ≤ value μ a z + price μ a z * (y - z) + (y - z) ^ 2 / (2 * μ) := by
  apply sub_le_iff_le_add'.mp
  apply (le_div_iff₀ (mul_pos zero_lt_two hμ)).mpr
  have h := first_order (z := z) hμ (price_le (μ := μ) (a := a) (z := y))
  unfold value
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos hμ.le h,
    sq_nonneg (μ * (price μ a y - price μ a z) - (y - z))]

theorem value_drain (hμ : 0 < μ) (hth : μ * a ≤ y) (hyz : y ≤ z) :
    value μ a y + (z - y) * a ≤ value μ a z := by
  have h (w : ℝ) (hw : μ * a ≤ w) : price μ a w = a :=
    min_eq_left ((le_div_iff₀ hμ).mpr (by rwa [mul_comm]))
  rw [value, value, h y hth, h z (hth.trans hyz)]
  linarith

end Scalar

variable {I : Type*} [Fintype I]

def potential (μ : ℝ) (a : I → ℝ) (z : I → ℕ) : ℝ :=
  ∑ i, value μ (a i) (z i)

variable {μ : ℝ} {a : I → ℝ} {y z : I → ℕ}

theorem potential_nonneg (hμ : 0 < μ) (ha : ∀ i, 0 ≤ a i) : 0 ≤ potential μ a z :=
  Finset.sum_nonneg (fun i _ => value_nonneg hμ (ha i))

theorem potential_zero (ha : ∀ i, 0 ≤ a i) : potential μ a 0 = 0 := by
  simp [potential, value_zero (ha _)]

theorem potential_close (hμ : 0 < μ) :
    ∑ i, a i * z i ≤ potential μ a z + μ * (∑ i, a i ^ 2) / 2 := by
  rw [potential, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => value_close hμ)

theorem potential_increment (hμ : 0 < μ) :
    potential μ a y ≤ potential μ a z + (∑ i, price μ (a i) (z i) * ((y i : ℝ) - z i)) +
      (∑ i, ((y i : ℝ) - z i) ^ 2) / (2 * μ) := by
  rw [potential, potential, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => value_increment hμ)

theorem potential_drain (hμ : 0 < μ) (hyz : ∀ i, y i ≤ z i)
    (hth : ∀ i, y i < z i → μ * a i ≤ y i) :
    potential μ a y + ∑ i, ((z i : ℝ) - y i) * a i ≤ potential μ a z := by
  rw [potential, potential, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rcases (hyz i).eq_or_lt with he | hl
  · simp [he]
  · exact value_drain hμ (hth i hl) (Nat.cast_le.mpr hl.le)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local tensor substitution rates

Strict comparisons can first be made with a separate rational rate at
each spectral point. A finite subcover and a common denominator replace
all these rates by integer powers with the same number of demands.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open scoped NNReal

private theorem round_rate {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hp : 0 ≤ p) (h : a * p < b * q) :
    ∃ d n : ℕ, 0 < d ∧ (d : ℝ) * a < n * b ∧ (n : ℝ) * p < d * q := by
  have gap : 0 < q - a / b * p := by
    rw [sub_pos, div_mul_eq_mul_div, div_lt_iff₀ hb, mul_comm q]
    exact h
  obtain ⟨d, hd⟩ := exists_nat_gt (p / (q - a / b * p))
  have hd0 : 0 < d := Nat.cast_pos.mp ((div_nonneg hp gap.le).trans_lt hd)
  rw [div_lt_iff₀ gap] at hd
  let n := ⌊(d : ℝ) * (a / b)⌋₊ + 1
  refine ⟨d, n, hd0, ?_, ?_⟩
  · rw [← div_lt_iff₀ hb, mul_div_assoc]
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((d : ℝ) * (a / b))
  · have hn : (n : ℝ) ≤ (d : ℝ) * (a / b) + 1 := by
      simp only [n, Nat.cast_add, Nat.cast_one]
      exact add_le_add_left (Nat.floor_le (by positivity)) _
    calc
      _ ≤ ((d : ℝ) * (a / b) + 1) * p := mul_le_mul_of_nonneg_right hn hp
      _ < _ := by linarith

open Spectral

variable {K S I : Type} [Field K] [Fintype S]

private structure Offer (price : I → ℝ) (L : ℝ) where
  good : I
  demand : ℕ
  supply : ℕ
  positive : 0 < demand
  cheaper : (supply : ℝ) * price good < (demand : ℝ) * L

/-- The supplies can be raised to powers strictly cheaper than a common
power of the demand, yet at each spectral point some supply is worth more. -/
theorem finite_offers (D : Tensor K S) (T : I → Tensor K S)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) {L : ℝ}
    (hD : 1 ≤ D)
    (gap : ∀ v : Tensor K S →+* ℝ≥0, Monotone v →
      ∃ i, 1 < v (T i) ∧ Real.log (v D) * p i < Real.log (v (T i)) * L) :
    ∃ (J : Type) (_ : Fintype J) (b : ℕ) (t : J → I) (n : J → ℕ),
      0 < b ∧ (∀ j, (n j : ℝ) * p (t j) < (b : ℝ) * L) ∧
      ∀ v : Tensor K S →+* ℝ≥0, Monotone v → ∃ j, v D ^ b < v (T (t j)) ^ n j := by
  classical
  let U (o : Offer p L) : Set (Tensor K S → ℝ≥0) :=
    {v | v (D ^ o.demand) < v (T o.good ^ o.supply)}
  have ho (o) : IsOpen (U o) := isOpen_lt (continuous_apply _) (continuous_apply _)
  have hu : Spectrum.points (Tensor K S) ⊆ ⋃ o, U o := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨i, hi, hg⟩ := gap v hv
    have hd' : (1 : ℝ) ≤ v D := by exact_mod_cast (show 1 ≤ v D by simpa using hv hD)
    have hi' : (1 : ℝ) < v (T i) := hi
    obtain ⟨d, n, hd, hdn, hc⟩ :=
      round_rate (Real.log_nonneg hd') (Real.log_pos hi') (hp i) hg
    refine Set.mem_iUnion.mpr ⟨⟨i, d, n, hd, hc⟩, ?_⟩
    change v (D ^ d) < v (T i ^ n)
    rw [map_pow, map_pow, ← NNReal.coe_lt_coe, NNReal.coe_pow, NNReal.coe_pow,
      ← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    exact hdn
  obtain ⟨s, hs⟩ := (Spectrum.compact_points Tensor.exists_bound).elim_finite_subcover U ho hu
  let b := ∏ o ∈ s, o.demand
  have hb : 0 < b := Finset.prod_pos fun o _ => o.positive
  have each (j : s) : ∃ m, b = j.val.demand * m :=
    Finset.dvd_prod_of_mem (fun o => o.demand) j.property
  choose m hm using each
  have hm0 (j : s) : 0 < m j := by rw [hm j] at hb; exact Nat.pos_of_mul_pos_left hb
  refine ⟨s, inferInstance, b, fun j => j.val.good, fun j => j.val.supply * m j,
    hb, fun j => ?_, fun v hv => ?_⟩
  · rw [hm j, Nat.cast_mul, Nat.cast_mul, mul_right_comm, mul_right_comm _ (m j : ℝ)]
    exact mul_lt_mul_of_pos_right j.val.cheaper (Nat.cast_pos.mpr (hm0 j))
  · obtain ⟨o, hos, hov⟩ := Set.mem_iUnion₂.mp (hs ⟨v, hv, rfl⟩)
    change v (D ^ o.demand) < v (T o.good ^ o.supply) at hov
    rw [map_pow, map_pow] at hov
    let j : s := ⟨o, hos⟩
    refine ⟨j, ?_⟩
    rw [hm j, pow_mul, pow_mul]
    exact pow_lt_pow_left₀ hov zero_le (hm0 j).ne'

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A failed price test gives a strict spectral margin

Rescale each positive demand value to the total proposed price. Unless a
supply then exceeds its cap, every demand must be at its cap, contradicting
the failed test. A positive-price link handles zero demand values.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped NNReal

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S]

/-- A spectral test with demand coordinates marked for equality. -/
def Consistent (T : I → Tensor K S) (p : I → ℝ) (s : Finset I) : Prop :=
  ∃ (d : ℝ) (v : Tensor K S →+* ℝ), 0 ≤ d ∧ Monotone v ∧
    (∀ i, Tensor.values d v (T i) ≤ p i) ∧ ∀ i ∈ s, Tensor.values d v (T i) = p i

private theorem prod_unit_le (T : I → Tensor K S) (hT : ∀ i, T i ≠ 0) (s : Finset I) :
    1 ≤ ∏ i ∈ s, T i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    refine (Tensor.one_le _ (hT i)).trans ?_
    have hh := Tensor.mul_le_mul_left _ _ (T i) ih
    rw [mul_one] at hh
    exact hh

theorem failed_offers (T : I → Tensor K S) (hT : ∀ i, T i ≠ 0)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset I) (hL : 0 < ∑ i ∈ s, p i)
    (hpos : ∀ v : Tensor K S →+* ℝ, Monotone v → ∃ i, 1 < v (T i))
    (hfail : ¬ Consistent T p s) :
    ∃ (J : Type) (_ : Fintype J) (b : ℕ) (t : J → I) (n : J → ℕ),
      0 < b ∧ (∀ j, (n j : ℝ) * p (t j) < (b : ℝ) * (∑ i ∈ s, p i)) ∧
      ∀ v : Tensor K S →+* ℝ≥0, Monotone v →
        ∃ j, v (∏ i ∈ s, T i) ^ b < v (T (t j)) ^ n j := by
  classical
  let D := ∏ i ∈ s, T i
  let L := ∑ i ∈ s, p i
  have hD := prod_unit_le T hT s
  apply finite_offers D T p hp hD
  intro v hv
  let f := NNReal.toRealHom.comp v
  have hf : Monotone f := hv
  change ∃ i, (1 : ℝ) < f (T i) ∧ Real.log (f D) * p i < Real.log (f (T i)) * L
  have hD0 : 0 ≤ Real.log (f D) := Real.log_nonneg (by simpa only [map_one] using hf hD)
  rcases hD0.eq_or_lt with he | hg
  · obtain ⟨i, hi⟩ := hpos f hf
    exact ⟨i, hi, by rw [← he, zero_mul]; exact mul_pos (Real.log_pos hi) hL⟩
  let d := (L / Real.log (f D)) * Real.log 2
  have hd : 0 < d := mul_pos (div_pos hL hg) (Real.log_pos (by norm_num))
  have value i : Tensor.values d f (T i) = Real.log (f (T i)) * L / Real.log (f D) := by
    unfold Tensor.values d
    field_simp
  have ht i : 1 ≤ f (T i) := Tensor.value_one_le hf (hT i)
  have total : ∑ i ∈ s, Tensor.values d f (T i) = ∑ i ∈ s, p i := by
    simp only [value, div_eq_mul_inv, ← Finset.sum_mul]
    rw [← Real.log_prod (fun i _ => (zero_lt_one.trans_le (ht i)).ne'), ← map_prod]
    rw [← div_eq_mul_inv]
    exact mul_div_cancel_left₀ _ hg.ne'
  have bad : ¬ ∀ i, Tensor.values d f (T i) ≤ p i := by
    intro hall
    exact hfail ⟨d, f, hd.le, hf, hall,
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hall i)).mp total⟩
  push Not at bad
  obtain ⟨i, hi⟩ := bad
  rw [value, lt_div_iff₀ hg, mul_comm (p i)] at hi
  have hlog : 0 < Real.log (f (T i)) :=
    pos_of_mul_pos_left ((mul_nonneg hg.le (hp i)).trans_lt hi) hL.le
  exact ⟨i, (Real.log_pos_iff (zero_lt_one.trans_le (ht i)).le).mp hlog, hi⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Counting and pricing stock

Stocks are counts indexed by commodity. Collecting a list of orders by
commodity changes neither its tensor product nor the total price.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Stock

open Finset

variable {I J : Type} {S : Type*} [Fintype I] [Fintype J] [CommMonoid S]

def bundle (T : I → S) (z : I → ℕ) : S := ∏ i, T i ^ z i

def total (p : I → ℝ) (z : I → ℕ) : ℝ := ∑ i, (z i : ℝ) * p i

def collect [DecidableEq I] (g : J → I) (n : J → ℕ) (i : I) : ℕ :=
  ∑ j ∈ univ.filter (fun j => g j = i), n j

theorem bundle_add (T : I → S) (x y : I → ℕ) :
    bundle T (fun i => x i + y i) = bundle T x * bundle T y := by
  simp only [bundle, pow_add, prod_mul_distrib]

theorem total_add (p : I → ℝ) (x y : I → ℕ) :
    total p (fun i => x i + y i) = total p x + total p y := by
  simp only [total, Nat.cast_add, add_mul, sum_add_distrib]

theorem bundle_sum (T : I → S) (z : J → I → ℕ) (n : J → ℕ) :
    bundle T (fun i => ∑ j, z j i * n j) = ∏ j, bundle T (z j) ^ n j := by
  simp only [bundle, ← prod_pow_eq_pow_sum, pow_mul, ← prod_pow]
  exact prod_comm

theorem total_sum (p : I → ℝ) (z : J → I → ℕ) (n : J → ℕ) :
    total p (fun i => ∑ j, z j i * n j) = ∑ j, total p (z j) * n j := by
  simp only [total, Nat.cast_sum, Nat.cast_mul, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun i _ => by ring

variable [DecidableEq I]

theorem bundle_collect (T : I → S) (g : J → I) (n : J → ℕ) :
    bundle T (collect g n) = bundle (T ∘ g) n := by
  rw [bundle, bundle, ← prod_fiberwise univ g]
  apply prod_congr rfl
  intro i _
  rw [collect, ← prod_pow_eq_pow_sum]
  exact prod_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]

theorem total_collect (p : I → ℝ) (g : J → I) (n : J → ℕ) :
    total p (collect g n) = total (p ∘ g) n := by
  rw [total, total, ← sum_fiberwise univ g]
  apply sum_congr rfl
  intro i _
  rw [collect, Nat.cast_sum, sum_mul]
  exact sum_congr rfl fun j hj => by simp [(mem_filter.mp hj).2]

def copies (u : Finset I) (n : ℕ) (i : I) : ℕ := if i ∈ u then n else 0

theorem bundle_copies (T : I → S) (u : Finset I) (n : ℕ) :
    bundle T (copies u n) = (∏ i ∈ u, T i) ^ n := by
  simp [bundle, copies, apply_ite, prod_pow]

theorem total_copies (p : I → ℝ) (u : Finset I) (n : ℕ) :
    total p (copies u n) = n * ∑ i ∈ u, p i := by
  simp [total, copies, apply_ite, ite_mul, mul_sum]

end OAI.LinearAlgebra.MatrixExponent.Routing.Stock
end

section
/-!
# Products of a single finite digit alphabet

All tables in the closure assumptions have sizes bounded independently
of the height. In particular the same digit permutation and the same
product chart apply to every coordinate at every height.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform

abbrev length (M h : ℕ) := Nat.log M (2 ^ h)
abbrev spare (M h : ℕ) := (2 ^ h - 1) / M ^ (length M h) + 1
abbrev Words (M h : ℕ) := (Fin (length M h) → Fin M) × Fin (spare M h)

structure ProductChart (M : ℕ) where
  c : Fin (M + 1)
  a : Fin (M + 1)
  b : Fin (M + 1)
  split : Fin M ≃ Fin c.val × (Fin a.val × Fin b.val)

variable {M : ℕ}

instance : Finite (ProductChart M) := by
  let f : ProductChart M → Σ c a b : Fin (M + 1), Fin M ≃ Fin c.val × (Fin a.val × Fin b.val) :=
    fun p => ⟨p.c, p.a, p.b, p.split⟩
  apply Finite.of_injective f
  rintro ⟨c, a, b, e⟩ ⟨c', a', b', e'⟩ h
  cases h
  rfl

def ProductChart.apply (p : ProductChart M) (h : ℕ) :
    Words M h ≃ (Fin (length M h) → Fin p.c.val) ×
      ((Fin (length M h) → Fin p.a.val) × ((Fin (length M h) → Fin p.b.val) × Fin (spare M h))) where
  toFun x := (fun i => (p.split (x.1 i)).1, fun i => (p.split (x.1 i)).2.1,
    fun i => (p.split (x.1 i)).2.2, x.2)
  invFun y := (fun i => p.split.symm (y.1 i, y.2.1 i, y.2.2.1 i), y.2.2.2)
  left_inv x := by simp
  right_inv y := by simp

def digitPerm (p : Equiv.Perm (Fin M)) (h : ℕ) : Equiv.Perm (Words M h) where
  toFun x := (fun i => p (x.1 i), x.2)
  invFun x := (fun i => p.symm (x.1 i), x.2)
  left_inv x := by simp
  right_inv x := by simp

structure System (M : ℕ) (G : Type) [Group G] where
  read : ∀ h, Equiv.Perm (Words M h) → G →* Equiv.Perm (Words M h)
  fixed : Equiv.Perm (Fin M) → G
  read_fixed : ∀ h σ p, read h σ (fixed p) = digitPerm p h
  factor : ∀ (p : ProductChart M) (g : G),
    (∀ h σ x, (p.apply h (read h σ g x)).1 = (p.apply h x).1) →
    ∃ u v w : G, g = u * v * w ∧
      (∀ h σ x, (p.apply h (read h σ u x)).1 = (p.apply h x).1 ∧
        (p.apply h (read h σ u x)).2.1 = (p.apply h x).2.1) ∧
      (∀ h σ x, (p.apply h (read h σ v x)).1 = (p.apply h x).1 ∧
        (p.apply h (read h σ v x)).2.2 = (p.apply h x).2.2) ∧
      (∀ h σ x, (p.apply h (read h σ w x)).1 = (p.apply h x).1 ∧
        (p.apply h (read h σ w x)).2.1 = (p.apply h x).2.1)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
