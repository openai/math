import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Rational outer weights and their common denominator as the expert list changes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
open Finset
variable {E : Type*} [DecidableEq E]

/-- Score the incoming experts. Fresh experts receive scaled weight zero. -/
def scaledWeight (old : Finset E) (w : E → ℚ) (score : E → ℕ) (e : E) : ℚ :=
  if e ∈ old then 2 ^ score e * w e else 0

/-- Redistribute one sixty-fourth of the scaled weight over the current list. -/
def fixedShare (current : Finset E) (scaled : E → ℚ) (e : E) : ℚ :=
  if e ∈ current then
    (1 - 1 / 64) * scaled e + ((1 / 64) / current.card) * ∑ j ∈ current, scaled j
  else 0

def rootUpdate (old current : Finset E) (w : E → ℚ) (score : E → ℕ) : E → ℚ :=
  fixedShare current (scaledWeight old w score)

@[simp] theorem scaledWeight_of_mem {old : Finset E} {e : E} (he : e ∈ old)
    (w : E → ℚ) (score : E → ℕ) : scaledWeight old w score e = 2 ^ score e * w e :=
  ite_eq_left he

@[simp] theorem scaledWeight_of_notMem {old : Finset E} {e : E} (he : e ∉ old)
    (w : E → ℚ) (score : E → ℕ) : scaledWeight old w score e = 0 := ite_eq_right he

@[simp] theorem fixedShare_of_mem {current : Finset E} {e : E} (he : e ∈ current) (w : E → ℚ) :
    fixedShare current w e = (1 - 1 / 64) * w e + ((1 / 64) / current.card) * ∑ j ∈ current, w j :=
  ite_eq_left he

@[simp] theorem fixedShare_of_notMem {current : Finset E} {e : E} (he : e ∉ current) (w : E → ℚ) :
    fixedShare current w e = 0 := ite_eq_right he

theorem sum_fixedShare (current : Finset E) (w : E → ℚ) :
    ∑ e ∈ current, fixedShare current w e = ∑ e ∈ current, w e := by
  by_cases hc : current.Nonempty
  · have hcard : (current.card : ℚ) ≠ 0 := by exact_mod_cast hc.card_pos.ne'
    calc
      _ = ∑ e ∈ current, ((1 - 1 / 64) * w e + ((1 / 64) / current.card) * ∑ j ∈ current, w j) :=
        sum_congr rfl fun _ he => fixedShare_of_mem he w
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        field_simp
        ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp hc]

theorem fixedShare_pos {current : Finset E} {w : E → ℚ} {e : E} (he : e ∈ current)
    (hwe : 0 ≤ w e) (hW : 0 < ∑ j ∈ current, w j) : 0 < fixedShare current w e := by
  have hcard : (0 : ℚ) < current.card := by exact_mod_cast (card_pos.mpr ⟨e, he⟩)
  rw [fixedShare_of_mem he]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hwe)
    (mul_pos (div_pos (by norm_num) hcard) hW)

private theorem den_sum_dvd (s : Finset E) (x : E → ℚ) (Q : ℕ)
    (hx : ∀ e ∈ s, (x e).den ∣ Q) : (∑ e ∈ s, x e).den ∣ Q := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s hes ih =>
    rw [sum_insert hes]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (hx _ (mem_insert_self ..))
      (ih (fun x hxs => hx _ (mem_insert_of_mem hxs))))

theorem scaledWeight_den_dvd (old : Finset E) (w : E → ℚ) (score : E → ℕ) (Q : ℕ)
    (hQ : ∀ e ∈ old, (w e).den ∣ Q) (e : E) : (scaledWeight old w score e).den ∣ Q := by
  by_cases he : e ∈ old
  · rw [scaledWeight_of_mem he]
    have hden : ((2 : ℚ) ^ score e).den = 1 := by
      have hcast : (2 : ℚ) ^ score e = ((2 ^ score e : ℕ) : ℚ) := by push_cast; rfl
      rw [hcast, Rat.den_natCast]
    exact (Rat.mul_den_dvd _ _).trans (by simpa [hden] using hQ _ he)
  · simp [he]

/-- The updated common denominator includes just one factor of the enlarged list size. -/
theorem fixedShare_den_dvd (current : Finset E) (w : E → ℚ) (Q : ℕ)
    (hQ : ∀ e ∈ current, (w e).den ∣ Q) (e : E) :
    (fixedShare current w e).den ∣ Q * 64 * current.card := by
  by_cases he : e ∈ current
  · rw [fixedShare_of_mem he]
    have hcard : 0 < current.card := card_pos.mpr ⟨e, he⟩
    have hα : (1 / 64 : ℚ).den = 64 := by
      simpa only [one_div, Nat.cast_ofNat] using Rat.inv_natCast_den_of_pos (a := 64) (by decide)
    have hl : (1 - 1 / 64 : ℚ).den ∣ 64 :=
      (Rat.sub_den_dvd _ _).trans (by simp)
    have hs := den_sum_dvd current w Q hQ
    apply (Rat.add_den_dvd_lcm _ _).trans
    apply Nat.lcm_dvd
    · apply (Rat.mul_den_dvd _ _).trans
      exact (Nat.mul_dvd_mul hl (hQ _ he)).trans (by rw [Nat.mul_comm 64]; exact dvd_mul_right ..)
    · rw [div_eq_mul_inv (1 / 64 : ℚ)]
      apply (Rat.mul_den_dvd _ _).trans
      have hcoef : ((1 / 64 : ℚ) * (current.card : ℚ)⁻¹).den ∣ 64 * current.card := by
        simpa [hα, Rat.inv_natCast_den_of_pos hcard] using
          Rat.mul_den_dvd (1 / 64 : ℚ) (current.card : ℚ)⁻¹
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_dvd_mul hcoef hs
  · simp [he]

theorem rootUpdate_den_dvd (old current : Finset E) (w : E → ℚ) (score : E → ℕ) (Q : ℕ)
    (hQ : ∀ e ∈ old, (w e).den ∣ Q) (e : E) :
    (rootUpdate old current w score e).den ∣ Q * 64 * current.card :=
  fixedShare_den_dvd _ _ _ (fun j _ => scaledWeight_den_dvd _ _ _ _ hQ j) e

/-- The first trial splits one unit uniformly. -/
def initialWeight (experts : Finset E) (e : E) : ℚ :=
  if e ∈ experts then (experts.card : ℚ)⁻¹ else 0

def rootWeights (experts : ℕ → Finset E) (scores : ℕ → E → ℕ) : ℕ → E → ℚ
  | 0 => initialWeight (experts 0)
  | t + 1 => rootUpdate (experts t) (experts (t + 1)) (rootWeights experts scores t) (scores t)

def outerDenominator (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => m 0
  | t + 1 => outerDenominator m t * 64 * m (t + 1)

theorem rootWeights_den_dvd (experts : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ) (e : E) :
    (rootWeights experts scores t e).den ∣ outerDenominator (fun k => (experts k).card) t := by
  induction t generalizing e with
  | zero =>
    simp only [rootWeights, initialWeight, outerDenominator]
    split_ifs with he
    · rw [Rat.inv_natCast_den_of_pos (card_pos.mpr ⟨_, he⟩)]
    · simp
  | succ t ih =>
    exact rootUpdate_den_dvd _ _ _ _ _ (fun j _ => ih j) e

theorem outerDenominator_le (m : ℕ → ℕ) (M t : ℕ) (hm : ∀ i ≤ t, m i ≤ M) :
    outerDenominator m t ≤ M * (64 * M) ^ t := by
  induction t with
  | zero => simpa [outerDenominator] using hm 0 le_rfl
  | succ t ih =>
    have h := ih (fun i hi => hm i (Nat.le_succ_of_le hi))
    calc
      _ ≤ (M * (64 * M) ^ t * 64) * M := Nat.mul_le_mul (Nat.mul_le_mul_right 64 h) (hm _ le_rfl)
      _ = _ := by rw [pow_succ]; ring

/-- The denominator requires at most `b + (6+b)*t + 1` binary digits. -/
theorem outerDenominator_le_two_pow (m : ℕ → ℕ) (b t : ℕ)
    (hm : ∀ i ≤ t, m i ≤ 2 ^ b) : outerDenominator m t ≤ 2 ^ (b + (6 + b) * t) := by
  calc
    _ ≤ 2 ^ b * (64 * 2 ^ b) ^ t := outerDenominator_le _ _ _ hm
    _ = _ := by rw [pow_add, pow_mul, pow_add]; rfl

/-- Adding zero-weight experts before sharing cannot change the rescaled total. -/
theorem sum_rootUpdate (old current : Finset E) (ho : old ⊆ current)
    (w : E → ℚ) (s : E → ℕ) :
    ∑ e ∈ current, rootUpdate old current w s e = ∑ e ∈ old, (2 : ℚ) ^ s e * w e := by
  change ∑ e ∈ current, fixedShare current (scaledWeight old w s) e = _
  rw [sum_fixedShare, ← Finset.sum_subset ho (fun i _ hi => scaledWeight_of_notMem hi w s)]
  exact Finset.sum_congr rfl fun e he => scaledWeight_of_mem he w s

/-- The uniform first trial has unit mass. -/
theorem sum_initialWeight (s : Finset E) (hs : s.Nonempty) : ∑ e ∈ s, initialWeight s e = 1 := by
  calc
    _ = ∑ _e ∈ s, (s.card : ℚ)⁻¹ := Finset.sum_congr rfl fun _ h => ite_eq_left h
    _ = _ := by
      have hn : (s.card : ℚ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
      simp [sum_const, nsmul_eq_mul, hn]

theorem scaledWeight_nonneg {old : Finset E} {w : E → ℚ} (s : E → ℕ)
    (hw : ∀ e ∈ old, 0 ≤ w e) (e : E) : 0 ≤ scaledWeight old w s e := by
  by_cases he : e ∈ old
  · rw [scaledWeight_of_mem he]
    exact mul_nonneg (by positivity) (hw _ he)
  · simp [he]

theorem fixedShare_floor {current : Finset E} {w : E → ℚ} {e : E} (he : e ∈ current)
    (hw : 0 ≤ w e) :
    ((1 / 64 : ℚ) / current.card) * ∑ j ∈ current, w j ≤ fixedShare current w e := by
  rw [fixedShare_of_mem he]
  exact le_add_of_nonneg_left (mul_nonneg (by norm_num) hw)

theorem fixedShare_retained {current : Finset E} {w : E → ℚ} {e : E} (he : e ∈ current)
    (hw : ∀ j ∈ current, 0 ≤ w j) :
    (1 - (1 / 64 : ℚ)) * w e ≤ fixedShare current w e := by
  rw [fixedShare_of_mem he]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sum_nonneg hw))

/-- Every listed expert has positive weight, including the first time it appears. -/
theorem rootWeights_pos (lists : ℕ → Finset E) (scores : ℕ → E → ℕ)
    (hlists : ∀ t, (lists t).Nonempty) (hgrow : ∀ t, lists t ⊆ lists (t + 1)) (t : ℕ)
    {e : E} (he : e ∈ lists t) : 0 < rootWeights lists scores t e := by
  induction t generalizing e with
  | zero =>
    rw [rootWeights, initialWeight, ite_eq_left he]
    exact inv_pos.mpr (by exact_mod_cast (hlists 0).card_pos)
  | succ t ih =>
    let w := rootWeights lists scores t
    let v := scaledWeight (lists t) w (scores t)
    have hv : ∀ j, 0 ≤ v j := scaledWeight_nonneg _ (fun j hj => (ih hj).le)
    obtain ⟨i, hi⟩ := hlists t
    have hi' : 0 < v i := by
      dsimp [v]; rw [scaledWeight_of_mem hi]
      exact mul_pos (by positivity) (ih hi)
    exact fixedShare_pos he (hv e) (sum_pos' (fun j _ => hv j) ⟨i, hgrow t hi, hi'⟩)

end PriceGame
end LinearProgramming
end Optimization
end OAI
