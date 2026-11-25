import OAI.Computability.MultitapeWeakETH.Sparsification
import Mathlib.Data.Nat.Log

/-! # A dyadic, integer-computable choice of the sparsification budget -/

namespace OAI.Computability.MultitapeWeakETH

/-- One every q binary length bits contributes a doubling to the budget. -/
def sparseBudget (q n : ℕ) := 2^(Nat.log 2 n / q)

theorem sparseBudget_bounds {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    let s := sparseBudget q n
    (s:ℝ) ≤ (n:ℝ)^((q:ℝ)⁻¹) ∧ (n:ℝ)^((q:ℝ)⁻¹) ≤ 2*s := by
  let m := Nat.log 2 n
  let s := sparseBudget q n
  have small : s^q ≤ n := by
    dsimp [s,sparseBudget]
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self _ _)).trans (Nat.pow_log_le_self _ hn.ne')
  have large : n ≤ (2*s)^q := by
    dsimp [s,sparseBudget]
    rw [← pow_succ',← pow_mul]
    apply (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le.trans
    apply Nat.pow_le_pow_right (by decide)
    change m+1 ≤ (m/q+1)*q
    have h := Nat.mod_lt m hq
    have e := Nat.mod_add_div m q
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (m/q)]
    omega
  constructor
  · apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast small
  · apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast large

/-- The same fixed exponent saving absorbs both the number of visits and
the volume-dependent leaf search after width-three sparsification. -/
theorem sparse_clock {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ q : ℕ, 1 < q ∧ ∀ C : ℝ, 0 ≤ C → ∀ n : ℕ, 0 < n →
      let s := sparseBudget q n
      let η := (q:ℝ)⁻¹
      (n:ℝ)/s + (C*n*(s:ℝ)^4)^(1-δ) ≤ (2+C^(1-δ))*(n:ℝ)^(1-η) := by
  obtain ⟨q,hq⟩ := exists_nat_gt (8/δ)
  have large : 8 < (q:ℝ)*δ := (div_lt_iff₀ hδ).mp hq
  have qpos : (0:ℝ) < q := lt_trans (by positivity) hq
  have qtwo : (1:ℝ) < q := by nlinarith
  let η := (q:ℝ)⁻¹
  have pos : 0 < η := inv_pos.mpr qpos
  have saving : η ≤ δ/8 := by
    dsimp only [η]; rw [inv_eq_one_div,div_le_iff₀ qpos]; nlinarith
  have budget : (1+η*4)*(1-δ) ≤ 1-η := by nlinarith [mul_nonneg pos.le hδ.le]
  refine ⟨q,by exact_mod_cast qtwo,?_⟩
  intro C hC n hn s _
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have positive : (0:ℝ) < n := by positivity
  have sp : (0:ℝ) < s := by dsimp [s,sparseBudget]; positivity
  obtain ⟨lo,hi⟩ := sparseBudget_bounds (by exact_mod_cast qpos) hn
  have tree : (n:ℝ)/s ≤ 2*(n:ℝ)^(1-η) := by
    apply (div_le_iff₀ sp).mpr
    calc
      (n:ℝ) = (n:ℝ)^(1-η)*(n:ℝ)^η := by rw [← Real.rpow_add positive, sub_add_cancel,Real.rpow_one]
      _ ≤ (n:ℝ)^(1-η)*(2*s) := by gcongr
      _ = _ := by ring
  have leaf : (C*n*(s:ℝ)^4)^(1-δ) ≤ C^(1-δ)*(n:ℝ)^(1-η) := by
    calc
      _ ≤ (C*n*((n:ℝ)^η)^4)^(1-δ) := by gcongr
      _ = C^(1-δ)*(n:ℝ)^((1+η*4)*(1-δ)) := by
        rw [mul_assoc,Real.mul_rpow hC (by positivity),← Real.rpow_mul_natCast positive.le,
          ← Real.rpow_one_add' positive.le (by positivity),← Real.rpow_mul positive.le]
        norm_num
      _ ≤ _ := by gcongr
  calc
    _ ≤ 2*(n:ℝ)^(1-η)+C^(1-δ)*(n:ℝ)^(1-η) := add_le_add tree leaf
    _ = _ := by ring

end OAI.Computability.MultitapeWeakETH
