import OAI.Optimization.LinearProgramming.PriceGame.TrialWeightArithmetic
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionPackets

/-! Bit widths for the actual fractional allocations and all prefix sums of a signed gain. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

/-- All allocations for a single expert have a common denominator determined by
its integer supply. At zero supply the deterministic maximizer receives mass one. -/
theorem allocation_den_factor {ne ng : ℕ} (pos : Fin ne → Bool)
    (available : Fin ne → Fin ng → Bool) (bids : Fin ne → Fin ng → ℚ)
    (prices : Fin ng → ℚ) (qty : Fin ne → ℕ) (flow : Fin ne → Option (Fin ng) → ℕ)
    (e : Fin ne) (o : Option (Fin ng)) :
    (Market.allocation pos available bids prices qty flow e o).den ∣ max 1 (qty e) := by
  unfold Market.allocation
  by_cases h : qty e = 0
  · rw [ite_eq_left h]
    split <;> simp
  · rw [ite_eq_right h, Nat.max_eq_right (Nat.pos_of_ne_zero h)]
    apply (rat_den_dvd_iff_grid _ _).mpr
    refine ⟨flow e o, ?_⟩
    unfold Market.fraction
    have hn : (qty e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h
    push_cast
    field_simp

/-- One row denominator controls every good, including the outside option. -/
theorem commonUnit_fraction_den {N ne l : ℕ} (experts : Fin ne → Expert N)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (e : Fin ne)
    (o : Option (Vertex N l)) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    (A.fractions e o).den ∣ max 1 (Market.Denominator.qty (weightDenominator L) (L e)) := by
  exact allocation_den_factor _ _ _ _ _ _ e (o.map (vertexEquivFin N l))

/-- Multiplying by a binary sign and summing a subset keeps the common row denominator. -/
private theorem signed_grid {I : Type*} (s : Finset I) (f : I → ℚ) (sign : I → ℤ)
    (Q : ℕ) (hf : ∀ i ∈ s, (f i).den ∣ Q) :
    (∑ i ∈ s, f i * (sign i : ℚ)).den ∣ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi]
    apply (Rat.add_den_dvd_lcm _ _).trans
    apply Nat.lcm_dvd
    · exact (Rat.mul_den_dvd _ _).trans (by simpa using hf i (mem_insert_self ..))
    · exact ih (fun j hj => hf j (mem_insert_of_mem hj))

/-- `Q` is a supplied common denominator with at most `d` bits in the exponent
bound, and `2^b` bounds every incoming weight. Every fractional allocation and
every partial sum of a signed gain has a polynomial bound in `b+d`. -/
theorem market_fraction_gain_ratBits {N ne l : ℕ} (experts : Fin ne → Expert N)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (Q b d : ℕ)
    (hQ : 0 < Q) (hd : Q ≤ 2^d) (hl : WeightInputCap Q b L) (e : Fin ne)
    (labels : Vertex N l → Bool) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    (∀ o, RAM.ratBits (A.fractions e o) ≤ 3 + 2*(b+d)) ∧
    (∀ s : Finset (Vertex N l), RAM.ratBits (∑ i ∈ s, A.fractions e (some i) *
        sides experts e * labelSign (labels i)) ≤ 3 + 2*(b+d)) := by
  let A := marketSolverAtCommonWeightUnit experts l history L hL
  let D := weightDenominator L
  let row := max 1 (Market.Denominator.qty D (L e))
  have hrow : 0 < row := Nat.zero_lt_of_lt (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))
  have hD : D ≤ 2^d := (Nat.le_of_dvd hQ (weightDenominator_dvd L hl.den)).trans hd
  have hrowCap : row ≤ 2^(b+d) := by
    refine Nat.max_le.mpr ⟨Nat.one_le_pow _ _ (by decide), ?_⟩
    have hqty := Market.Denominator.cast_qty (Q:=D) (hL e) (den_dvd_weightDenominator L e)
    have hDr : (D : ℚ) ≤ 2^d := by exact_mod_cast hD
    have hq : (Market.Denominator.qty D (L e) : ℚ) ≤ 2^(b+d) := by
      rw [hqty, pow_add, mul_comm ((2 : ℚ)^b)]
      exact mul_le_mul hDr (hl.upper e) (hL e) (by positivity)
    exact_mod_cast hq
  have hden (o : Option (Vertex N l)) : (A.fractions e o).den ∣ row :=
    commonUnit_fraction_den experts history L hL e o
  have hfrac (o : Option (Vertex N l)) : |A.fractions e o| ≤ (2 : ℚ)^0 := by
    rw [abs_of_nonneg (A.balanced.nonneg e o), pow_zero, ← A.balanced.unit e]
    exact single_le_sum (fun i _ => A.balanced.nonneg e i) (mem_univ o)
  constructor
  · intro o
    simpa using (dyadic_encoding_bounds _ row 0 (b+d) hrow hrowCap (hden o) (hfrac o)).2.2
  · intro s
    let z (i : Vertex N l) : ℤ := if (experts e).skeleton.positive = labels i then 1 else -1
    have hz (i : Vertex N l) : sides experts e * labelSign (labels i) = (z i : ℚ) := by
      cases p : (experts e).skeleton.positive <;> cases q : labels i <;>
        simp [sides, Market.side, labelSign, z, p, q]
    have hs : (∑ i ∈ s, A.fractions e (some i) * sides experts e * labelSign (labels i)).den ∣ row := by
      simp only [mul_assoc, hz]
      exact signed_grid _ _ _ _ (fun i _ => hden (some i))
    have hmag : |∑ i ∈ s, A.fractions e (some i) * sides experts e * labelSign (labels i)| ≤ (2 : ℚ)^0 := by
      apply (abs_sum_le_sum_abs _ s).trans
      simp only [abs_mul, abs_of_nonneg (A.balanced.nonneg e _), sides_abs, labelSign_abs, mul_one, pow_zero]
      exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => A.balanced.nonneg e (some i))).trans
        (market_mass_le experts history L A e)
    simpa using (dyadic_encoding_bounds _ row 0 (b+d) hrow hrowCap hs hmag).2.2

/-- A nonnegative rational register lies inside the dyadic magnitude budget determined
by its concrete reduced-word encoding. -/
theorem weight_le_of_ratBits (q : ℚ) (hq : 0 ≤ q) {B : ℕ} (hb : RAM.ratBits q ≤ B) :
    q ≤ (2 : ℚ)^B := by
  have hn : (q.num : ℚ) = q * (q.den : ℚ) :=
    (div_eq_iff (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : ℚ) ≠ 0)).mp q.num_div_den
  have hd : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hk : q.num.natAbs.log2 + 1 ≤ B := by unfold RAM.ratBits at hb; omega
  calc
    q = q*1 := (mul_one _).symm
    _ ≤ q*(q.den : ℚ) := mul_le_mul_of_nonneg_left hd hq
    _ = (q.num : ℚ) := hn.symm
    _ ≤ (q.num.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]; exact le_abs_self _
    _ ≤ (2 : ℚ)^B := by
      exact_mod_cast (show q.num.natAbs < 2^(q.num.natAbs.log2+1) from Nat.lt_log2_self).le.trans (Nat.pow_le_pow_right (by decide) hk)

/-- Convert directly from routed register invariants to bounds for the shares and
partially accumulated signed sums returned inside this particular physical market call. -/
theorem market_fraction_gain_of_registers {N ne l : ℕ} (experts : Fin ne → Expert N)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (Q d B : ℕ)
    (hQ : 0 < Q) (hd : Q ≤ 2^d) (h : ∀ e, (L e).den ∣ Q ∧ RAM.ratBits (L e) ≤ B)
    (e : Fin ne) (labels : Vertex N l → Bool) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    (∀ o, RAM.ratBits (A.fractions e o) ≤ 3 + 2*(B+d)) ∧
    (∀ s : Finset (Vertex N l), RAM.ratBits (∑ i ∈ s, A.fractions e (some i) *
        sides experts e * labelSign (labels i)) ≤ 3 + 2*(B+d)) :=
  market_fraction_gain_ratBits experts history L hL Q B d hQ hd
    ⟨fun k => (h k).1, fun k => weight_le_of_ratBits (L k) (hL k) (h k).2⟩ e labels

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
