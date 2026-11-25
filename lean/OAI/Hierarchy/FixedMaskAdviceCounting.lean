import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI
/-! # Counting fixed strings for the port-coloring masks -/

namespace Hierarchy.FixedMaskAdvice

open Finset
open scoped BigOperators

noncomputable section

private def expect {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

private theorem expect_prod {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (f : I → A → ℝ) :
    expect (fun x : I → A => ∏ i, f i (x i)) = ∏ i, expect (f i) := by
  classical
  simp only [expect, ← Fintype.prod_sum f, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fun, Nat.cast_pow]

private theorem expect_sum {I A : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect (f i) := by
  unfold expect
  rw [Finset.sum_comm, Finset.sum_div]

private theorem expect_const {A : Type*} [Fintype A] [Nonempty A] (x : ℝ) :
    expect (fun _ : A => x) = x := by
  simp [expect, nsmul_eq_mul, Fintype.card_ne_zero]

private theorem expect_mono {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    expect f ≤ expect g := by
  exact div_le_div_of_nonneg_right (sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

abbrev Rows (B : ℕ) := Fin (B^2) × Fin (B^2)

/-- A row is blocked when at least half its positions belong to the obstruction set. -/
def blocked {B L : ℕ} (S : Finset (Fin B)) (x : Fin L → Fin B) : Prop :=
  L ≤ 2 * (univ.filter fun k => x k ∈ S).card

private def factor {B : ℕ} (S : Finset (Fin B)) (c : Fin B) : ℝ :=
  (if c ∈ S then 4 else 1) / 2

private def weight {B L : ℕ} (S : Finset (Fin B)) (x : Fin L → Fin B) : ℝ :=
  ∏ k, factor S (x k)

private theorem weight_nonneg {B L : ℕ} (S : Finset (Fin B)) (x : Fin L → Fin B) :
    0 ≤ weight S x := by
  apply prod_nonneg
  intro k _
  unfold factor
  split <;> norm_num

private theorem weight_ge_one {B L : ℕ} {S : Finset (Fin B)} {x : Fin L → Fin B}
    (h : blocked S x) : 1 ≤ weight S x := by
  unfold weight factor
  rw [Finset.prod_div_distrib, Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one, card_univ, Fintype.card_fin]
  apply (one_le_div (by positivity)).mpr
  calc (2:ℝ)^L ≤ 2^(2*(univ.filter fun i => x i ∈ S).card) := pow_le_pow_right₀ (by norm_num) h
       _ = _ := by rw [pow_mul]; norm_num

private theorem factor_mean {B : ℕ} (hB : 0 < B) (S : Finset (Fin B)) (hs : 4*S.card ≤ B) :
    expect (factor S) ≤ 7/8 := by
  have pos : (0:ℝ) < B := by exact_mod_cast hB
  have H : (4:ℝ)*S.card ≤ B := by exact_mod_cast hs
  have Hsum : ∑ c : Fin B, (if c ∈ S then (4:ℝ) else 1) = B + 3*(S.card : ℝ) := by
    have e (c : Fin B) : (if c ∈ S then (4:ℝ) else 1) = 1 + (if c ∈ S then 3 else 0) := by
      split <;> norm_num
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, ← Finset.sum_filter]
    simp [mul_comm]
  unfold expect factor
  rw [Fintype.card_fin, ← Finset.sum_div, Hsum]
  apply (div_le_iff₀ pos).mpr
  linarith

private theorem weight_mean {B L : ℕ} (hB : 0<B) (S : Finset (Fin B)) (hs : 4*S.card≤B) :
    expect (weight (L:=L) S) ≤ (7/8)^L := by
  unfold weight
  rw [expect_prod (fun _ : Fin L => factor S)]
  simp only [prod_const, card_univ, Fintype.card_fin]
  apply pow_le_pow_left₀ _ (factor_mean hB S hs)
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sum_nonneg
  intro c _
  unfold factor
  split <;> norm_num

private def witness {B L : ℕ} (S : Finset (Fin B)) (T : Finset (Rows B))
    (x : Rows B → Fin L → Fin B) : ℝ :=
  ∏ j, if j ∈ T then weight S (x j) else 1

private theorem witness_nonneg {B L : ℕ} (S : Finset (Fin B)) (T : Finset (Rows B))
    (x : Rows B → Fin L → Fin B) : 0 ≤ witness S T x := by
  apply prod_nonneg
  intro j _
  split
  · exact weight_nonneg _ _
  · norm_num

private theorem witness_mean {B L : ℕ} (hB : 0<B) (S : Finset (Fin B)) (hs : 4*S.card≤B)
    (T : Finset (Rows B)) : expect (witness (L:=L) S T) ≤ ((7/8)^L)^T.card := by
  classical
  let : NeZero B := ⟨hB.ne'⟩
  unfold witness
  rw [expect_prod (fun j (x : Fin L → Fin B) => if j ∈ T then weight S x else 1)]
  have e (j : Rows B) : expect (fun x : Fin L → Fin B => if j∈T then weight S x else 1) =
      if j ∈ T then expect (weight (L:=L) S) else 1 := by
    by_cases hj : j ∈ T <;> simp [hj, expect_const]
  simp only [e, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  have eqT : univ.filter (· ∈ T) = T := by ext; simp
  rw [eqT]
  apply pow_le_pow_left₀ _ (weight_mean hB S hs)
  exact div_nonneg (sum_nonneg (fun x _ => weight_nonneg _ x)) (Nat.cast_nonneg _)

set_option maxHeartbeats 1600000 in
/-- The first-moment bound for all obstruction sets and all choices of `B` overloaded rows. -/
theorem exists_of_union_bound {B L : ℕ} (hB : 0<B)
    (gap : (2:ℝ)^B * ((B:ℝ)^4)^B * (((7:ℝ)/8)^L)^B < 1) :
    ∃ str : Rows B → Fin L → Fin B, ∀ S : Finset (Fin B), 4*S.card≤B →
      (univ.filter fun j => L ≤ 2*(univ.filter fun k => str j k ∈ S).card).card < B := by
  classical
  let : NeZero B := ⟨hB.ne'⟩
  let sets := univ.filter (fun S : Finset (Fin B) => 4*S.card≤B)
  let groups := (univ : Finset (Rows B)).powersetCard B
  let cost (x : Rows B → Fin L → Fin B) := ∑ S ∈ sets, ∑ T ∈ groups, witness S T x
  have csets : sets.card ≤ 2^B := by
    simpa [sets] using Finset.card_le_univ sets
  have cgroups : groups.card ≤ (B^4)^B := by
    have cardR : Fintype.card (Rows B) = B^4 := by simp [Rows]; ring
    simpa [groups, cardR, Finset.card_powersetCard] using Nat.choose_le_pow (Fintype.card (Rows B)) B
  have E : expect cost < 1 := by
    calc
      expect cost = ∑ S ∈ sets, ∑ T ∈ groups, expect (witness (L:=L) S T) := by
        unfold cost
        rw [expect_sum]
        apply sum_congr rfl
        intro S _
        exact expect_sum groups (witness S)
      _ ≤ ∑ _S ∈ sets, ∑ _T ∈ groups, (((7:ℝ)/8)^L)^B := by
        apply sum_le_sum
        intro S hS
        apply sum_le_sum
        intro T hT
        have cardT : T.card = B := (Finset.mem_powersetCard.mp hT).2
        exact (witness_mean (L:=L) hB S (Finset.mem_filter.mp hS).2 T).trans_eq
          (congrArg (fun n : ℕ => (((7:ℝ)/8)^L)^n) cardT)
      _ = sets.card * (groups.card * ((((7:ℝ)/8)^L)^B)) := by simp [nsmul_eq_mul]
      _ ≤ (2:ℝ)^B * (((B:ℝ)^4)^B * (((7:ℝ)/8)^L)^B) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact_mod_cast csets
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast cgroups
      _ = (2:ℝ)^B * ((B:ℝ)^4)^B * (((7:ℝ)/8)^L)^B := by ring
      _ < 1 := gap
  have ex : ∃ x, cost x < 1 := by
    by_contra! h
    have H := expect_mono h
    rw [expect_const] at H
    linarith
  obtain ⟨x,hx⟩ := ex
  refine ⟨x, fun S hS => ?_⟩
  by_contra! bad
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq bad
  have hgood : 1 ≤ witness S T x := by
    apply Finset.one_le_prod₀
    intro j _
    by_cases hj : j ∈ T
    · simp only [ite_eq_left hj]
      exact weight_ge_one (mem_filter.mp (hT hj)).2
    · simp [hj]
  have hs : S ∈ sets := Finset.mem_filter.mpr ⟨mem_univ _,hS⟩
  have ht : T ∈ groups := Finset.mem_powersetCard.mpr ⟨subset_univ _,hcard⟩
  apply (not_le_of_gt hx)
  exact hgood.trans ((single_le_sum (f:=fun t => witness S t x) (fun t _ => witness_nonneg _ _ _) ht).trans
    (single_le_sum (f:=fun s => ∑ t ∈ groups, witness s t x)
      (fun s _ => sum_nonneg (fun t _ => witness_nonneg _ _ _)) hs))

end

end Hierarchy.FixedMaskAdvice

end OAI
