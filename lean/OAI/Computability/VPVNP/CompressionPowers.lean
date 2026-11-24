import OAI.Computability.VPVNP.CompressionProcedure

/-!
# Repeating an exact compressor block

Theorem 7.1 of *VP and VNP differ over every field* repeats the same block
along every branch of its tensor expansion. For the energy estimate (7.4),
adding a fixed multiple of the squared position count to the energy makes
this quantity contract by a factor of four at each block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Procedure

variable {R : Type*} [CommSemiring R] {a k κ : ℕ} {μ : ℝ} (P : Procedure R a a k κ μ)

/-- Execute the same block `T` times, consuming `T*k` lanes and retaining
`g` unused lanes. Each continuation receives its own selected output state. -/
def repeatExecution (g : ℕ) : (T n : ℕ) → n = T * k + g → (X : State a n) →
    StateExecution R a g X
  | 0, n, h, X => (Procedure.id R a).run g n (by simpa using h) X
  | t + 1, n, h, X =>
    let E := P.run (t * k + g) n (by rw [h, Nat.succ_mul]; omega) X
    E.bind fun z => repeatExecution g t (t * k + g) rfl (E.finalState z)

/-- Every final branch has the exact position count after `T` blocks. -/
theorem repeat_positions (g T n : ℕ) (h : n = T * k + g) (X : State a n) :
    ∀ z, X.positions = κ ^ T * ((P.repeatExecution g T n h X).finalState z).positions := by
  induction T generalizing n with
  | zero =>
    intro z
    exact (Procedure.id R a).positions g n (by simpa using h) X z
  | succ t ih =>
    let E := P.run (t * k + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact E.forall_final_bind
      (fun z => P.repeatExecution g t (t * k + g) rfl (E.finalState z))
      (fun Y => X.positions = κ ^ (t + 1) * Y.positions) fun z y => by
        rw [P.positions _ _ _ X z, ih _ rfl (E.finalState z) y, pow_succ', Nat.mul_assoc]

/-- Coefficient of the squared position count in the contracting quantity. -/
noncomputable def potentialWeight : ℝ := 4 * P.error / (1 - 4 / (κ : ℝ) ^ 2)

private theorem denominator_pos (hκ : 2 < κ) : 0 < 1 - 4 / (κ : ℝ) ^ 2 := by
  have h : (2 : ℝ) < κ := by exact_mod_cast hκ
  have hsq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg κ)).mpr h
  apply sub_pos.mpr
  apply (div_lt_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < κ))).mpr
  linarith only [hsq]

theorem potentialWeight_nonneg (hκ : 2 < κ) : 0 ≤ P.potentialWeight :=
  div_nonneg (mul_nonneg (by norm_num) P.error_nonneg) (denominator_pos hκ).le

private theorem balance (hκ : 2 < κ) :
    P.potentialWeight * ((κ : ℝ) ^ 2 - 4) = 4 * P.error * (κ : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < κ := by exact_mod_cast P.divisor_pos
  have h := div_mul_cancel₀ (4 * P.error) (denominator_pos hκ).ne'
  change P.potentialWeight * (1 - 4 / (κ : ℝ) ^ 2) = 4 * P.error at h
  rw [← h, mul_assoc, sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero _ hpos.ne')]

/-- A single block contracts the energy plus the squared-position correction. -/
theorem potential_step (hκ : 2 < κ) (hμ : μ ≤ 1 / 4) (g n : ℕ) (h : n = k + g)
    (X : State a n) (z : (P.run g n h X).Choices) :
    let Y := (P.run g n h X).finalState z
    4 * (Y.energy + P.potentialWeight * (Y.positions : ℝ) ^ 2) ≤
      X.energy + P.potentialWeight * (X.positions : ℝ) ^ 2 := by
  let Y := (P.run g n h X).finalState z
  have hpos : (X.positions : ℝ) = (κ : ℝ) * Y.positions := by exact_mod_cast P.positions g n h X z
  have hen : Y.energy ≤ μ * X.energy + P.error * (X.positions : ℝ) ^ 2 := P.energy g n h X z
  have hcoeff := mul_le_mul_of_nonneg_right hμ X.energy_nonneg
  change 4 * (Y.energy + P.potentialWeight * (Y.positions : ℝ) ^ 2) ≤ _
  rw [hpos] at hen ⊢
  have hbal := congrArg (fun c : ℝ => c * (Y.positions : ℝ) ^ 2) (P.balance hκ)
  nlinarith only [hcoeff, hen, hbal]

/-- The scaled contracting quantity along the actual branch-dependent execution. -/
theorem repeat_scaled_potential (hκ : 2 < κ) (hμ : μ ≤ 1 / 4) (g T n : ℕ) (h : n = T * k + g)
    (X : State a n) : ∀ z, let Y := (P.repeatExecution g T n h X).finalState z
      (4 : ℝ) ^ T * (Y.energy + P.potentialWeight * (Y.positions : ℝ) ^ 2) ≤
        X.energy + P.potentialWeight * (X.positions : ℝ) ^ 2 := by
  induction T generalizing n with
  | zero =>
    intro z
    let E := (Procedure.id R a).run g n (by simpa using h) X
    have hc : X.positions = (E.finalState z).positions := by
      simpa only [one_mul] using (Procedure.id R a).positions g n (by simpa using h) X z
    have he : (E.finalState z).energy ≤ X.energy := by
      have he := (Procedure.id R a).energy g n (by simpa using h) X z
      change (E.finalState z).energy ≤ 1 * X.energy + 0 * (X.positions : ℝ) ^ 2 at he
      simpa only [one_mul, zero_mul, add_zero] using he
    change (4 : ℝ) ^ 0 * ((E.finalState z).energy +
      P.potentialWeight * ((E.finalState z).positions : ℝ) ^ 2) ≤ _
    rw [pow_zero, one_mul, ← hc]
    exact add_le_add he le_rfl
  | succ t ih =>
    let E := P.run (t * k + g) n (by rw [h, Nat.succ_mul]; omega) X
    exact E.forall_final_bind
      (fun z => P.repeatExecution g t (t * k + g) rfl (E.finalState z))
      (fun Y => (4 : ℝ) ^ (t + 1) * (Y.energy + P.potentialWeight * (Y.positions : ℝ) ^ 2) ≤
        X.energy + P.potentialWeight * (X.positions : ℝ) ^ 2) fun z y => by
        rw [pow_succ', mul_assoc]
        exact (mul_le_mul_of_nonneg_left (ih _ rfl (E.finalState z) y) (by norm_num)).trans
          (P.potential_step hκ hμ _ _ _ X z)

/-- Equation (7.4), with the coefficient of the initial position count given
explicitly. The first inequality controls all final shared wire fields. -/
theorem repeat_totalWidth_le (hκ : 2 < κ) (hμ : μ ≤ 1 / 4) (g T n : ℕ) (h : n = T * k + g)
    (X : State a n) (z : (P.repeatExecution g T n h X).Choices) :
    let Y := (P.repeatExecution g T n h X).finalState z
    (Y.totalWidth : ℝ) ≤ √Y.energy ∧
      √Y.energy ≤ (√X.energy + √P.potentialWeight * X.positions) / (2 : ℝ) ^ T := by
  let Y := (P.repeatExecution g T n h X).finalState z
  refine ⟨Y.totalWidth_le_sqrt, ?_⟩
  have hstep := P.repeat_scaled_potential hκ hμ g T n h X z
  have hB := P.potentialWeight_nonneg hκ
  have hscale : (4 : ℝ) ^ T * Y.energy ≤ X.energy + P.potentialWeight * (X.positions : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hB (sq_nonneg _)))
      (by positivity : 0 ≤ (4 : ℝ) ^ T)).trans hstep
  have hsq : ((2 : ℝ) ^ T) ^ 2 = 4 ^ T := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ T)).mpr
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)))).mp
  rw [mul_pow, Real.sq_sqrt Y.energy_nonneg, hsq, add_sq, mul_pow,
    Real.sq_sqrt X.energy_nonneg, Real.sq_sqrt hB]
  linarith only [hscale, mul_nonneg (Real.sqrt_nonneg X.energy)
    (mul_nonneg (Real.sqrt_nonneg P.potentialWeight) (Nat.cast_nonneg X.positions))]

/-- The history attached to the repeated execution gives the exact finite
sum of its expanded kernel paths for every assignment of initial factors. -/
theorem repeat_contract (g T n : ℕ) (h : n = T * k + g) (X : State a n)
    (F : NetworkKernel.Factors R X.network) :
    let H := (P.repeatExecution g T n h X).history
    NetworkKernel.contract X.network F = ∑ path : H.Path, H.weight F path :=
  (P.repeatExecution g T n h X).history.contract_eq_sum_paths F

/-- For an input with at least `T*k` lanes, keep exactly the unused suffix.
This is the lane-count convention in Theorem 7.1. -/
def repeatWithLanes (T n : ℕ) (h : T * k ≤ n) (X : State a n) :
    StateExecution R a (n - T * k) X :=
  P.repeatExecution (n - T * k) T n (Nat.add_sub_of_le h).symm X

/-- Position count and final wire bound for every term, starting with any
number of lanes that suffices for the chosen repetition count. -/
theorem repeatWithLanes_bounds (hκ : 2 < κ) (hμ : μ ≤ 1 / 4) (T n : ℕ) (h : T * k ≤ n)
    (X : State a n) (z : (P.repeatWithLanes T n h X).Choices) :
    let Y := (P.repeatWithLanes T n h X).finalState z
    X.positions = κ ^ T * Y.positions ∧ (Y.totalWidth : ℝ) ≤ √Y.energy ∧
      √Y.energy ≤ (√X.energy + √P.potentialWeight * X.positions) / (2 : ℝ) ^ T :=
  ⟨P.repeat_positions _ _ _ _ X z, P.repeat_totalWidth_le hκ hμ _ _ _ _ X z⟩

end Compression.Procedure

end VPVNP
end Computability
end OAI
