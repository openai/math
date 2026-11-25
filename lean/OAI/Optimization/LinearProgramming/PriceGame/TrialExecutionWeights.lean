import OAI.Optimization.LinearProgramming.PriceGame.MomentRational

/-! Replaying a prefix of an adaptive trial gives the weights available when the
next query was chosen. The statements cover both the probe phase and the final
phase, where the local updates have already stopped. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

namespace Moment

open Finset

theorem localWeightQ_congr_prefix {E : Type*} (η : ℚ) (w : E → ℚ)
    {g g' : ℕ → E → ℚ} (t : ℕ) (e : E) (h : ∀ i < t, g i e = g' i e) :
    localWeightQ η w g t e = localWeightQ η w g' t e := by
  unfold localWeightQ
  congr 1
  exact prod_congr rfl fun i hi => by rw [h i (mem_range.mp hi)]

theorem deepWeightQ_congr_prefix {E : Type*} (w : E → ℚ)
    {s s' : ℕ → E → ℕ} (t : ℕ) (e : E) (h : ∀ i < t, s i e = s' i e) :
    deepWeightQ w s t e = deepWeightQ w s' t e := by
  unfold deepWeightQ
  rw [sum_congr rfl fun i hi => h i (mem_range.mp hi)]

@[simp] theorem localWeightQ_zero {E : Type*} (η : ℚ) (w : E → ℚ)
    (g : ℕ → E → ℚ) (e : E) : localWeightQ η w g 0 e = w e := by
  simp [localWeightQ]

theorem localWeightQ_succ {E : Type*} (η : ℚ) (w : E → ℚ)
    (g : ℕ → E → ℚ) (t : ℕ) (e : E) :
    localWeightQ η w g (t + 1) e = localWeightQ η w g t e * (1 + η * g t e) := by
  simp [localWeightQ, prod_range_succ, mul_assoc]

@[simp] theorem deepWeightQ_zero {E : Type*} (w : E → ℚ)
    (s : ℕ → E → ℕ) (e : E) : deepWeightQ w s 0 e = w e := by
  simp [deepWeightQ]

theorem deepWeightQ_succ {E : Type*} (w : E → ℚ) (s : ℕ → E → ℕ) (t : ℕ) (e : E) :
    deepWeightQ w s (t + 1) e = deepWeightQ w s t e * 2 ^ s t e := by
  simp [deepWeightQ, sum_range_succ, pow_add, mul_assoc]

theorem localWeightQ_positive {E : Type*} {η : ℚ} (hη : 0 ≤ η) (hη' : η < 1)
    {w : E → ℚ} (g : ℕ → E → ℚ) (t : ℕ) (e : E) (hw : 0 < w e)
    (hg : ∀ i < t, |g i e| ≤ 1) : 0 < localWeightQ η w g t e := by
  apply mul_pos hw
  apply prod_pos
  intro i hi
  have hgain := (abs_le.mp (hg i (mem_range.mp hi))).1
  have hmul := mul_le_mul_of_nonneg_left hgain hη
  linarith

theorem deepWeightQ_positive {E : Type*} {w : E → ℚ} (s : ℕ → E → ℕ)
    (t : ℕ) (e : E) (hw : 0 < w e) : 0 < deepWeightQ w s t e :=
  mul_pos hw (pow_pos (by norm_num) _)

end Moment

namespace TrialExecution

open Moment

/-- Restrict a table of answers to the first (j) entries. -/
def takePrefix {n : ℕ} {A : Type*} (xs : Fin n → A) (j : ℕ) (hj : j ≤ n) :
    Fin j → A := fun i => xs ⟨i, lt_of_lt_of_le i.isLt hj⟩

def prefixAt {n : ℕ} {A : Type*} (xs : Fin n → A) (j : Fin n) : Fin j.val → A :=
  takePrefix xs j.val j.isLt.le

theorem probeAt_takePrefix_map {A B : Type*} [Zero B] {n : ℕ} (xs : Fin n → A)
    (f : A → B) (j : ℕ) (hj : j ≤ n) {t : ℕ} (ht : t < j) :
    probeAt (fun i => f (takePrefix xs j hj i)) t = probeAt (fun i => f (xs i)) t := by
  simp [probeAt, takePrefix, ht, lt_of_lt_of_le ht hj]

theorem probeAt_prefixAt_map {A B : Type*} [Zero B] {n : ℕ} (xs : Fin n → A)
    (f : A → B) (j : Fin n) {t : ℕ} (ht : t < j.val) :
    probeAt (fun i => f (prefixAt xs j i)) t = probeAt (fun i => f (xs i)) t :=
  probeAt_takePrefix_map xs f j.val j.isLt.le ht

/-- Local weights may stop after the probe phase. Restricting to any already
available prefix gives the same weights at every earlier update. -/
theorem localWeightQ_takePrefix {A E : Type*} {n : ℕ} (xs : Fin n → A) (f : A → E → ℚ)
    (η : ℚ) (w : E → ℚ) (j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k ≤ j) (e : E) :
    localWeightQ η w (probeAt fun i => f (takePrefix xs j hj i)) k e =
      localWeightQ η w (probeAt fun i => f (xs i)) k e := by
  apply localWeightQ_congr_prefix
  intro i hi
  exact congrFun (probeAt_takePrefix_map xs f j hj (hi.trans_le hk)) e

/-- Deeper experts receive a multiplier from each of the two groups of child calls. -/
theorem deepWeightQ_takePrefix {A E : Type*} {n : ℕ} (xs : Fin n → A) (f : A → E → ℕ)
    (w : E → ℚ) (j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k ≤ j) (e : E) :
    deepWeightQ w (probeAt fun i => f (takePrefix xs j hj i)) k e =
      deepWeightQ w (probeAt fun i => f (xs i)) k e := by
  apply deepWeightQ_congr_prefix
  intro i hi
  exact congrFun (probeAt_takePrefix_map xs f j hj (hi.trans_le hk)) e

theorem localWeightQ_prefixAt {A E : Type*} {n : ℕ} (xs : Fin n → A) (f : A → E → ℚ)
    (η : ℚ) (w : E → ℚ) (j : Fin n) (e : E) :
    localWeightQ η w (probeAt fun i => f (prefixAt xs j i)) j.val e =
      localWeightQ η w (probeAt fun i => f (xs i)) j.val e :=
  localWeightQ_takePrefix xs f η w j.val j.isLt.le j.val le_rfl e

theorem deepWeightQ_prefixAt {A E : Type*} {n : ℕ} (xs : Fin n → A) (f : A → E → ℕ)
    (w : E → ℚ) (j : Fin n) (e : E) :
    deepWeightQ w (probeAt fun i => f (prefixAt xs j i)) j.val e =
      deepWeightQ w (probeAt fun i => f (xs i)) j.val e :=
  deepWeightQ_takePrefix xs f w j.val j.isLt.le j.val le_rfl e

end TrialExecution

end PriceGame
end LinearProgramming
end Optimization
end OAI
