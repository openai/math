import OAI.Hierarchy.TickResourceBounds

namespace OAI
/-! # Word-table and setup-clock cost of the factor compiler -/

namespace Hierarchy.FactorBucketRAM

open Filter GridScale

def ticks (w N d : ℕ) := 3+N*d*(20*(w+1)+1)*24 + (3+N*d*22) +
  (3+(20*(w+1)+2)^d*7) + (3+N*16)

/-- The public threshold table is width-dependent and is paid bit-for-bit.
Its literal encoding uses one native word for each threshold. -/
theorem threshold_bits (w : ℕ) : (20*(w+1)+1)*(64*w) ≤ 1344*(w+1)^2 := by nlinarith

def budgetConstant (d : ℕ) := 526*d+28+7*22^d

theorem clock_bound (w N d : ℕ) : ticks w N d ≤ budgetConstant d*(w+1)^(d+1)*(N+1) := by
  let p := (w+1)^(d+1)
  have wp : w+1≤p := by
    calc
      w+1 = (w+1)^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have pp : 1≤p := by omega
  have grow : N+1 ≤ (N+1)*p := Nat.le_mul_of_pos_right _ (by omega)
  have sm : 20*(w+1)+1 ≤ 21*p := by omega
  have first : N*d*(20*(w+1)+1) ≤ (N+1)*p*(21*d) := calc
    _ ≤ (N+1)*d*(21*p) := Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ _)) sm
    _ = _ := by ring
  have second : N*d ≤ (N+1)*p*d := Nat.mul_le_mul_right _ (by omega)
  have bd : (20*(w+1)+2)^d ≤ 22^d*p := calc
    _ ≤ (22*(w+1))^d := Nat.pow_le_pow_left (by omega) _
    _ = 22^d*(w+1)^d := Nat.mul_pow _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have third : (20*(w+1)+2)^d ≤ (N+1)*p*22^d := bd.trans (by
    have mult : p≤(N+1)*p := Nat.le_mul_of_pos_left _ (by omega)
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (22^d) mult)
  change ticks w N d ≤ budgetConstant d*p*(N+1)
  unfold ticks budgetConstant
  nlinarith only [first,second,third,grow,show 1≤(N+1)*p by omega]

/-- Rebuilding the complete assignments, even at every receiver, fits the
shorter true dyadic tick clock. -/
theorem fits_receiver {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    (k A d c₀ : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → ∀ N : ℕ, (N:ℝ)≤((2:ℝ)^w)^(4/5:ℝ) →
      ticks w N d ≤ 2^(w-((w^c₀).log2+1)) := by
  filter_upwards [receiver_setup_room env k A (budgetConstant d) (d+1) c₀] with w h
  intro q hq hQ N size
  have paid := h q hq hQ
  have pin : 1≤pins w (overhead Q D w) := Nat.one_le_of_lt (Nat.pow_pos (by decide : 0<2))
  have size' : (N:ℝ)+1 ≤ ((2:ℝ)^w)^(4/5:ℝ)+(pins w (overhead Q D w):ℝ) :=
    add_le_add size (by exact_mod_cast pin)
  exact_mod_cast (show (ticks w N d : ℝ) ≤ (2^(w-((w^c₀).log2+1)):ℕ) from calc
    _ ≤ ((budgetConstant d*(w+1)^(d+1):ℕ):ℝ)*((N:ℝ)+1) := by exact_mod_cast clock_bound w N d
    _ ≤ _ := (mul_le_mul_of_nonneg_left size' (by positivity)).trans paid)

end Hierarchy.FactorBucketRAM

end OAI
