import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-! The sign-dependent masses, truncation depth, and terminal prices in Section 4.2. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace States
namespace Mass

open Finset

/-- Coordinates at a node after a given number of duplications. -/
def Vertex (n : ℕ) : ℕ → Type
  | 0 => Fin n
  | l + 1 => Vertex n l × Bool

instance vertexFintype (n : ℕ) : (l : ℕ) → Fintype (Vertex n l)
  | 0 => inferInstanceAs (Fintype (Fin n))
  | l + 1 => by
    letI := vertexFintype n l
    exact inferInstanceAs (Fintype (Vertex n l × Bool))

def depth (n : ℕ) : ℕ := n.log2 + 1

/-- The copy matching the sign is eight times as heavy, and the other has half the mass. -/
def factor (h tag : Bool) : ℚ := if tag = h then 8 else 1 / 2

def weight (n : ℕ) : (l : ℕ) → Bool → Vertex n l → ℚ
  | 0, _, _ => 1 / n
  | l + 1, h, (i, tag) => factor h tag * weight n l h i

theorem weight_nonneg (n l : ℕ) (h : Bool) (i : Vertex n l) :
    0 ≤ weight n l h i := by
  induction l with
  | zero => dsimp [weight]; positivity
  | succ l ih =>
    change 0 ≤ factor h i.2 * weight n l h i.1
    apply mul_nonneg _ (ih i.1)
    unfold factor
    split <;> norm_num

/-- Number of successive copies whose tags match this sign. -/
def matchingTags (n : ℕ) : (l : ℕ) → Bool → Vertex n l → ℕ
  | 0, _, _ => 0
  | l + 1, h, (i, tag) => matchingTags n l h i + if tag = h then 1 else 0

theorem matchingTags_le (n l : ℕ) (h : Bool) (i : Vertex n l) : matchingTags n l h i ≤ l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    obtain ⟨i, tag⟩ := i
    have hprev := ih i
    simp only [matchingTags]
    split <;> omega

/-- All weights at depth `l` have the same available denominator. Each matching copy
multiplies the corresponding integer numerator by sixteen. -/
theorem weight_dyadic (n l : ℕ) (h : Bool) (i : Vertex n l) :
    weight n l h i = (16 : ℚ) ^ matchingTags n l h i / ((n : ℚ) * 2 ^ l) := by
  induction l with
  | zero => simp [weight, matchingTags]
  | succ l ih =>
    obtain ⟨i, tag⟩ := i
    simp only [weight, matchingTags, ih, factor]
    split <;> simp [pow_succ, div_eq_mul_inv] <;> ring

/-- Explicit numerators have at most `4*l+1` binary digits. -/
theorem numerator_le (n l : ℕ) (h : Bool) (i : Vertex n l) :
    (16 : ℕ) ^ matchingTags n l h i ≤ 2 ^ (4 * l) := by
  calc
    (16 : ℕ) ^ matchingTags n l h i ≤ 16 ^ l := Nat.pow_le_pow_right (by decide) (matchingTags_le n l h i)
    _ = 2 ^ (4 * l) := by rw [pow_mul]; rfl

theorem weight_product (n l : ℕ) (i : Vertex n l) :
    weight n l true i * weight n l false i = 4 ^ l / (n : ℚ) ^ 2 := by
  induction l with
  | zero => simp [weight, pow_two]
  | succ l ih =>
    obtain ⟨i, tag⟩ := i
    change (factor true tag * weight n l true i) * (factor false tag * weight n l false i) = _
    have hf : factor true tag * factor false tag = 4 := by cases tag <;> norm_num [factor]
    rw [mul_mul_mul_comm, hf, ih, pow_succ]
    ring

theorem depth_first (n l : ℕ) (hn : 0 < n) (i : Vertex n l) :
    1 < weight n l true i * weight n l false i ↔ depth n ≤ l := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  rw [weight_product, lt_div_iff₀ (sq_pos_of_pos hnq), one_mul]
  have hp : (4 : ℚ) ^ l = ((2 : ℚ) ^ l) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [hp, sq_lt_sq₀ (le_of_lt hnq) (by positivity)]
  change (n : ℚ) < 2 ^ l ↔ n.log2 + 1 ≤ l
  exact_mod_cast (Nat.log2_lt (k := l) hn.ne').symm

theorem card_vertices (n l : ℕ) : Fintype.card (Vertex n l) = 2 ^ l * n := by
  induction l with
  | zero => change Fintype.card (Fin n) = _; simp
  | succ l ih =>
    change Fintype.card (Vertex n l × Bool) = _
    rw [Fintype.card_prod, Fintype.card_bool, ih, pow_succ]
    ring

theorem card_vertices_le (n l : ℕ) (hn : 0 < n) (hl : l ≤ depth n) :
    Fintype.card (Vertex n l) ≤ 2 * n ^ 2 := by
  rw [card_vertices]
  have hpow : 2 ^ l ≤ 2 ^ depth n := Nat.pow_le_pow_right (by decide) hl
  have hdepth : 2 ^ depth n ≤ 2 * n := by
    rw [depth, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.log2_self_le hn.ne')
  calc
    2 ^ l * n ≤ (2 * n) * n := Nat.mul_le_mul_right n (hpow.trans hdepth)
    _ = 2 * n ^ 2 := by ring

def leafPrice (n : ℕ) (upper : ℚ) (i : Vertex n (depth n)) : ℚ :=
  if weight n (depth n) true i ≤ 1 then upper else -upper

theorem root_mass_le_one (n : ℕ) (hn : 0 < n) (h : Bool) (S : Finset (Fin n)) :
    ∑ i ∈ S, weight n 0 h i ≤ 1 := by
  have hc := S.card_le_univ
  rw [Fintype.card_fin] at hc
  simp only [weight, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  apply (div_le_one (by exact_mod_cast hn)).2
  exact_mod_cast hc

/-- The leaf's mass test gives the correct signed price simultaneously for every possible state. -/
theorem leafPrice_signed (n : ℕ) (hn : 0 < n) (upper : ℚ) (h : Bool)
    (i : Vertex n (depth n)) (hi : weight n (depth n) h i ≤ 1) :
    (if h then leafPrice n upper i else -leafPrice n upper i) = upper := by
  have hprod := (depth_first n (depth n) hn i).2 le_rfl
  cases h with
  | true => simp [leafPrice, hi]
  | false =>
    have hnpos : ¬weight n (depth n) true i ≤ 1 := by
      intro hpos
      have hle := mul_le_mul_of_nonneg_right hpos (weight_nonneg n (depth n) false i)
      rw [one_mul] at hle
      exact (not_lt_of_ge (hle.trans hi)) hprod
    simp [leafPrice, hnpos]

theorem leaf_succeeds (n : ℕ) (hn : 0 < n) (upper shift : ℚ) (h : Bool)
    (S : Finset (Vertex n (depth n))) (P : Vertex n (depth n) → ℚ)
    (hS : ∑ i ∈ S, weight n (depth n) h i ≤ 1)
    (hP : ∀ i ∈ S, P i ≤ upper) (ht : 0 ≤ shift) (i : Vertex n (depth n)) (hi : i ∈ S) :
    P i - shift ≤ (if h then leafPrice n upper i else -leafPrice n upper i) := by
  have hmass : weight n (depth n) h i ≤ 1 :=
    (Finset.single_le_sum (f := weight n (depth n) h) (fun j _ => weight_nonneg n (depth n) h j) hi).trans hS
  rw [leafPrice_signed n hn upper h i hmass]
  exact (sub_le_self _ ht).trans (hP i hi)

section Active
variable {ι : Type*} [DecidableEq ι]

/-- The cheap copy of every active vertex, and the matching copy of each strict violator. -/
def childActive (h : Bool) (S U : Finset ι) : Finset (ι × Bool) :=
  (S ×ˢ {!h}) ∪ (U ×ˢ {h})

theorem sum_childActive (w : ι → ℚ) (h : Bool) (S U : Finset ι) :
    ∑ v ∈ childActive h S U, factor h v.2 * w v.1 =
      1 / 2 * (∑ i ∈ S, w i) + 8 * (∑ i ∈ U, w i) := by
  have hdis : Disjoint (S ×ˢ {!h}) (U ×ˢ {h}) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have a : p.2 = !h := by simpa using (Finset.mem_product.mp hp).2
    have b : p.2 = h := by simpa using (Finset.mem_product.mp hq).2
    cases h <;> simp_all
  unfold childActive
  rw [Finset.sum_union hdis, Finset.sum_product, Finset.sum_product]
  cases h <;> simp [factor, Finset.mul_sum]

theorem child_mass_le_one (w : ι → ℚ) (h : Bool) (S U : Finset ι)
    (hS : ∑ i ∈ S, w i ≤ 1) (hU : ∑ i ∈ U, w i ≤ 1 / 16) :
    ∑ v ∈ childActive h S U, factor h v.2 * w v.1 ≤ 1 := by
  rw [sum_childActive]
  linarith

/-- At a shifted threshold only coordinates whose previous surplus strictly exceeds the
pivot surplus keep a second copy. -/
def violators (S : Finset ι) (threshold : ι → ℚ) (shift : ℚ) : Finset ι :=
  S.filter (fun i => shift < threshold i)

theorem transition_admissible (w : ι → ℚ) (h : Bool) (S : Finset ι)
    (threshold : ι → ℚ) (shift : ℚ)
    (hS : ∑ i ∈ S, w i ≤ 1)
    (hviol : ∑ i ∈ violators S threshold shift, w i ≤ 1 / 16) :
    ∑ v ∈ childActive h S (violators S threshold shift), factor h v.2 * w v.1 ≤ 1 :=
  child_mass_le_one w h S _ hS hviol

theorem maximum_pivot_admissible (w : ι → ℚ) (h : Bool) (S : Finset ι)
    (threshold : ι → ℚ) (t : ℚ) (hS : ∑ i ∈ S, w i ≤ 1)
    (hpos : ∃ i ∈ S, t < threshold i) :
    ∃ j ∈ S, t < threshold j ∧ (∀ i ∈ S, threshold i ≤ threshold j) ∧
      ∑ v ∈ childActive h S (violators S threshold (threshold j)), factor h v.2 * w v.1 ≤ 1 := by
  obtain ⟨i, hi, hi'⟩ := hpos
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image threshold ⟨i, hi⟩
  refine ⟨j, hj, hi'.trans_le (hmax i hi), hmax, transition_admissible w h S threshold _ hS ?_⟩
  have hempty : violators S threshold (threshold j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    obtain ⟨hk, hgt⟩ := Finset.mem_filter.mp hk
    exact (not_lt_of_ge (hmax k hk)) hgt
  rw [hempty, Finset.sum_empty]
  norm_num

end Active

end Mass
end States
end PriceGame
end LinearProgramming
end Optimization
end OAI
