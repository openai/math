import OAI.Optimization.LinearProgramming.PriceGame.TrialRecursiveWeightBounds
import OAI.Optimization.LinearProgramming.PriceGame.FixedShareActualAllReplies
import OAI.Optimization.LinearProgramming.PriceGame.WeightCapPolynomial

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

open TrialExecution Moment States.Mass Learning

/-- All trials up to time `T` share this per-register encoding bound. -/
def campaignWeightBits (N R T : ℕ) : ℕ :=
  let a := catalogueBits N R T
  weightBits N probes (depth N) T (a + (6+a)*T)

/-- This applies to the actual outer trajectory, including inconsistent replies to
repeated queries. Its conclusion includes every deeper and local vector throughout
the next trial and preserves the exact shared denominator on every deeper branch. -/
theorem actual_round_weight_registers {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val = ((trialLoop (Pool.batch N R)
      (runRound R (fun experts => marketSolverAtCommonWeightUnit experts))
      T (Population.start (Pool.batch N R))).run reply history) j)
    (t : ℕ) (ht : t ≤ T) :
    let p := population R out t
    let D := populationDenominator R out t
    WeightRegistersWithin probes R (populationExperts p) D (D * etaQ.den ^ probes)
      (campaignWeightBits N R T) (depth N) 0 .root (fun _ _ => 0)
      (populationWeights p) p.nonnegative := by
  let p := population R out t
  let D := populationDenominator R out t
  let a := catalogueBits N R T
  have h (i : Fin p.experts.length) := run_population_guard anchor R T
    (fun experts => marketSolverAtCommonWeightUnit experts) reply history out hx t ht i
  obtain ⟨k, hk⟩ := population_nonempty anchor R out t
  let i : Fin p.experts.length := ⟨k, Finset.mem_range.mp hk⟩
  have hD : 0 < D := (h i).1
  have hd : D ≤ 2^(a+(6+a)*T) :=
    (h i).2.1.trans <| Nat.pow_le_pow_right (by decide)
      (Nat.add_le_add_left (Nat.mul_le_mul_left (6+a) ht) a)
  have cap : WeightInputCap D T (populationWeights p) := ⟨fun i => (h i).2.2.1, fun i =>
    (h i).2.2.2.2.1.trans (pow_le_pow_right₀ (by norm_num) ht)⟩
  exact weightRegistersWithin_of_cap probes R (populationExperts p) (depth N) 0 .root
    (fun _ _ => 0) _ p.nonnegative hD hd cap (Nat.zero_lt_of_lt anchor.isLt) le_rfl

/-- A single ordinary polynomial in `N + R.size + 1` that bounds every weight encoding
when the paper's fixed trial exponent 300 is used. -/
noncomputable def registerWeightPolynomial : Polynomial ℕ :=
  registerPolynomialAt 300 274 probes learningRateBits Pool.catalogueExponent

set_option maxRecDepth 8192 in
set_option exponentiation.threshold 1024 in
theorem campaignWeightBits_polynomial (N R T : ℕ) (hT : T ≤ (N + R.size + 1)^300) :
    campaignWeightBits N R T ≤ registerWeightPolynomial.eval (N + R.size + 1) := by
  let x := N + R.size + 1
  have hwidth (n : ℕ) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  have hn : N ≤ x := by dsimp [x]; omega
  have hdepth : depth N ≤ x + 1 := Nat.succ_le_succ ((Nat.log2_le_self N).trans hn)
  have hcat : catalogueBits N R T ≤ (x + x^300 + 1) * Pool.catalogueExponent := by
    unfold catalogueBits
    apply Nat.mul_le_mul_right
    have h1 : (N + R.size + 1).size ≤ x := hwidth _
    have h2 := (hwidth (T+1)).trans (Nat.succ_le_succ hT)
    change (N + R.size + 1).size + (T+1).size ≤ x+x^300+1
    change (T+1).size ≤ x^300+1 at h2
    exact (Nat.add_le_add h1 h2).trans (le_of_eq (Nat.add_assoc x (x^300) 1).symm)
  change campaignWeightBits N R T ≤ registerWeightPolynomial.eval x
  rw [registerWeightPolynomial, eval_registerPolynomialAt]
  unfold campaignWeightBits weightBits weightLayerBits
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add hT (Nat.mul_le_mul hdepth
      (Nat.mul_le_mul_left (2*probes) (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hn) 274)))) probes) 3)
    (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.add_le_add hcat
      (Nat.mul_le_mul (Nat.add_le_add_left hcat 6) hT)) (learningRateBits*probes)))

private theorem registers_weaken_bits (r R : ℕ) {N ne : ℕ} (experts : Fin ne → Expert N)
    (Q localQ B B' : ℕ) (hb : B ≤ B') :
    ∀ fuel l (path : States.Path (Fin N) (Vertex N l)) (history : History N)
      (w : Weights ne) (hw : ∀ e, 0 ≤ w e),
      WeightRegistersWithin r R experts Q localQ B fuel l path history w hw →
        WeightRegistersWithin r R experts Q localQ B' fuel l path history w hw := by
  intro fuel
  induction fuel with
  | zero =>
    intro l path history w hw h e
    exact ⟨(h e).1, (h e).2.trans hb⟩
  | succ fuel ih =>
    intro l path history w hw h
    refine ⟨fun e => ⟨(h.1 e).1, (h.1 e).2.trans hb⟩,
      Computation.guarded_mono h.2 (fun _ _ => True.intro) ?_⟩
    intro xs hx
    constructor
    · intro t ht e
      have he := hx.1 t ht e
      exact ⟨⟨he.1.1, he.1.2.trans hb⟩, ⟨he.2.1, he.2.2.trans hb⟩⟩
    · intro j
      exact ih _ _ _ _ _ (hx.2 j)

/-- A prefix is charged to the final public horizon, using observations only through the
current round. This is the count needed before future rounds have been run. -/
theorem population_length_at_prefix {N : ℕ} (anchor : Fin N) (R T : ℕ) (out : ℕ → RoundResult N)
    (t : ℕ) (ht : t ≤ T) (obs : ∀ j<t, (out j).observations.length ≤ Pool.probeBudget N) :
    (population R out t).experts.length ≤ ((N+R.size+1)*(T+1))^Pool.catalogueExponent :=
  (population_length_of_observations anchor R t out obs t le_rfl).trans
    (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.succ_le_succ ht)) _)

theorem population_binary_at_prefix {N : ℕ} (anchor : Fin N) (R T : ℕ) (out : ℕ → RoundResult N)
    (t : ℕ) (ht : t ≤ T) (obs : ∀ j<t, (out j).observations.length ≤ Pool.probeBudget N) :
    (population R out t).experts.length ≤ 2^catalogueBits N R T := by
  have hs : (t+1).size ≤ (T+1).size :=
    Nat.size_le.mpr ((Nat.succ_le_succ ht).trans_lt (Nat.lt_size_self (T+1)))
  exact (population_length_le_pow_two anchor R t out obs t le_rfl).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.add_le_add_left hs _)))

/-- Register theorem usable by a suspended trajectory: an actual prefix supplies the
past moment and observation facts, even if no representation of its future is stored. -/
theorem prefix_weight_registers_polynomial {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (hT : T ≤ (N+R.size+1)^300) (out : ℕ → RoundResult N) (t : ℕ) (ht : t≤T)
    (hs : ∀ j<t, PublicRoundBounds (population R out j) (out j)) :
    let p := population R out t
    let D := populationDenominator R out t
    WeightRegistersWithin probes R (populationExperts p) D (D*etaQ.den^probes)
      (registerWeightPolynomial.eval (N+R.size+1)) (depth N) 0 .root (fun _ _ => 0)
      (populationWeights p) p.nonnegative := by
  let p := population R out t
  let a := catalogueBits N R T
  let D := populationDenominator R out t
  have hDen : D ≤ 2^(a+(6+a)*T) := (populationDenominator_le R out t a
    (population_binary_at_prefix anchor R T out t ht (fun j hj => (hs j hj).observations))).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left (6+a) ht) a))
  have hCap : WeightInputCap D T (populationWeights p) := ⟨population_weight_den_dvd R out t, fun i =>
    (population_weight_le_sum R out t i).trans <|
      (population_total_le_of_moments anchor R out t (fun j hj => (hs j hj).moment)).trans
        (pow_le_pow_right₀ (by norm_num) ht)⟩
  apply registers_weaken_bits probes R _ _ _ _ _ (campaignWeightBits_polynomial N R T hT)
    _ _ _ _ _ _
  exact weightRegistersWithin_of_cap probes R (populationExperts p) (depth N) 0 .root
    (fun _ _ => 0) _ p.nonnegative (populationDenominator_pos anchor R out t) hDen hCap
    (Nat.zero_lt_of_lt anchor.isLt) le_rfl

/-- The full recursive register guarantee with a fixed polynomial evaluated at the
original dimensions and the binary length of the cost bound. -/
theorem actual_round_weight_registers_polynomial {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (hT : T ≤ (N + R.size + 1)^300)
    (reply : List (Query N × Bool) → Query N → Bool) (history : List (Query N × Bool))
    (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val = ((trialLoop (Pool.batch N R)
      (runRound R (fun experts => marketSolverAtCommonWeightUnit experts))
      T (Population.start (Pool.batch N R))).run reply history) j)
    (t : ℕ) (ht : t ≤ T) :
    let p := population R out t
    let D := populationDenominator R out t
    WeightRegistersWithin probes R (populationExperts p) D (D * etaQ.den ^ probes)
      (registerWeightPolynomial.eval (N + R.size + 1)) (depth N) 0 .root (fun _ _ => 0)
      (populationWeights p) p.nonnegative :=
  registers_weaken_bits probes R _ _ _ _ _ (campaignWeightBits_polynomial N R T hT)
    _ _ _ _ _ _ (actual_round_weight_registers anchor R T reply history out hx t ht)

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
