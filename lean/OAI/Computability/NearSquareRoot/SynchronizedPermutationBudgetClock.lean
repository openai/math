import OAI.Computability.NearSquareRoot.InterchangeLogSlack
import OAI.Computability.NearSquareRoot.Asymptotic
import OAI.Computability.NearSquareRoot.PrecisionWalshWidth
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-! # Time and visited cells of the synchronized permutation passes

A single layer uses a quadratic number of passes in the address logarithm.
Each pass has a volume-dependent clock and a polynomial header cost. The strict
exponent gap absorbs their total cost, uniformly over the physical volume. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open Filter IntegerMultiplication

private theorem count_log (k : ℕ) :
    1+(Nat.clog 2 (k+1):ℝ) ≤ (2+(Real.log 2)⁻¹) * (1+Real.log (1+(k:ℝ))) := by
  have scale := clog_le_logScale (Nat.succ_pos k)
  have h : (Nat.clog 2 (k+1):ℝ) ≤ (max 1 (Nat.clog 2 (k+1)):ℕ) := by
    exact_mod_cast Nat.le_max_right 1 _
  have upper := h.trans scale
  unfold logScale at upper
  push_cast at upper
  rw [add_comm (k:ℝ) 1] at upper
  have hl := Real.log_nonneg (show 1 ≤ 1+(k:ℝ) by simp)
  linarith only [upper,hl]

/-- The two logarithmic factors from the stage count preserve any prescribed strict
exponent allowance, including the setup work repeated at every stage. -/
theorem eventually_layer_clock (G : ℕ) (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (h d : ℕ) {ρ α : ℝ} (hρ : 0 ≤ ρ) (hρα : ρ < α) :
    ∀ᶠ k : ℕ in atTop, ∀ (V count : ℕ), 2^k ≤ V →
      count ≤ G * (1 + Nat.clog 2 (k+1))^2 →
      (count:ℝ) * (C * V * (1+(k:ℝ))^ρ * (1+Real.log (2+(k:ℝ)))^h +
        P * (1+(k:ℝ))^d) ≤ 2 * V * (1+(k:ℝ))^α := by
  let B : ℝ := 2+(Real.log 2)⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let c := (G:ℝ)*B^2*C*2^h
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have tends : Tendsto (fun k : ℕ => 1+(k:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have main := tends.eventually (eventually_logSlack c hc (h+2) hρα)
  have setup := eventually_polynomial_le_array_length ((G:ℝ)*B^2*P) (by positivity) (d+2)
  filter_upwards [main,setup] with k hm hs
  intro V count capacity stages
  let X : ℝ := 1+k
  let L := 1+Real.log X
  have hx : 1 ≤ X := by dsimp [X]; simp
  have hpos : 0 < X := zero_lt_one.trans_le hx
  have hlog := Real.log_nonneg hx
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hL' : L ≤ X := by dsimp [L]; linarith [Real.log_le_sub_one_of_pos hpos]
  have hcount : (count:ℝ) ≤ G*(B*L)^2 := by
    have hcast : (count:ℝ) ≤ G*(1+(Nat.clog 2 (k+1):ℝ))^2 := by exact_mod_cast stages
    exact hcast.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (count_log k) 2) (by positivity))
  have shifted : 1+Real.log (2+(k:ℝ)) ≤ 2*L := by
    have hle : 2+(k:ℝ) ≤ 2*X := by dsimp [X]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hl := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) hpos.ne'] at hl
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
    dsimp only [L]; linarith
  have hshift : 0 ≤ 1+Real.log (2+(k:ℝ)) := by
    linarith [Real.log_nonneg (show 1 ≤ 2+(k:ℝ) by linarith [Nat.cast_nonneg (α:=ℝ) k])]
  have hshiftPow := pow_le_pow_left₀ hshift shifted h
  have hp : 0 ≤ X^ρ := Real.rpow_nonneg hpos.le _
  have e₁ : (count:ℝ) * (C*V*X^ρ*(1+Real.log (2+(k:ℝ)))^h) ≤ V*X^α := by
    calc
      _ ≤ (G*(B*L)^2) * (C*V*X^ρ*(2*L)^h) := by gcongr
      _ = V*(c*L^(h+2)*X^ρ) := by
        dsimp [c]
        rw [mul_pow (2 : ℝ) L h, pow_add L h 2]
        ring
      _ ≤ V*X^α := mul_le_mul_of_nonneg_left hm (by positivity)
  have hcount' : (count:ℝ) ≤ G*(B*X)^2 := by
    apply hcount.trans
    gcongr
  have e₂ : (count:ℝ) * (P*X^d) ≤ V*X^α := by
    calc
      _ ≤ G*(B*X)^2*(P*X^d) := by gcongr
      _ = G*B^2*P*X^(d+2) := by rw [pow_add]; ring
      _ ≤ (2:ℝ)^k := hs
      _ ≤ (V:ℝ) := by exact_mod_cast capacity
      _ ≤ V*X^α := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hx (hρ.trans hρα.le))
  change (count:ℝ) * (C*V*X^ρ*(1+Real.log (2+(k:ℝ)))^h + P*X^d) ≤ 2*V*X^α
  rw [mul_add]; linarith

/-- Sequential passes sharing a tape interval pay for its visited cells only once.
The zero-pass case includes the initial head positions. -/
theorem fenced_layer {A Q I : Type} [Fintype I] (m : TM.Rule A Q I) (lo hi : I → ℤ)
    (boundary : ℕ → TM.Config A Q I) (ticks : ℕ → ℕ) (n : ℕ)
    (initial : ∀ i, lo i ≤ ((boundary 0).tape i).pos ∧ ((boundary 0).tape i).pos ≤ hi i)
    (pass : ∀ j < n, FencedRun m lo hi (boundary j) (ticks j) (boundary (j+1)))
    (clock : ℝ) (charge : ∀ j < n, (ticks j:ℝ) ≤ clock) :
    ∃ t : ℕ, (t:ℝ) ≤ n*clock ∧ Trace (TM.advance m) (boundary 0) t (boundary n) ∧
      VisitsAtMost m (boundary 0) t (∑ i, (hi i + 1 - lo i).toNat) := by
  have fenced : FencedRun m lo hi (boundary 0) (∑ j ∈ Finset.range n, ticks j) (boundary n) := by
    induction n with
    | zero =>
      constructor
      · simpa using (Trace.nil (step := TM.advance m) (boundary 0))
      · intro u hu z tr i
        have hu' : u = 0 := by simpa using hu
        subst u
        rw [trace_endpoint_unique tr (.nil _)]
        exact initial i
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (ih (fun j hj => pass j (by omega)) (fun j hj => charge j (by omega))).trans (pass n (by omega))
  refine ⟨_,?_,fenced.1,fenced.visitsAtMost⟩
  push_cast
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    (Finset.sum_le_sum (fun j hj => charge j (Finset.mem_range.mp hj)))

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
