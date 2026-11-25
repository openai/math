import OAI.Geometry.Hirsch.Potential
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Superpolynomial graph diameter of simple polytopes

Theorem 1.1 gives one family for each prescribed subpolynomial face-move allowance.
Specializing to edges gives `graph_diameter_beats_polynomials`, where the same family
works for every real polynomial. Theorem 1.2 instead prescribes dimension and facet excess.

The construction and its numerical layer bound follow *Superpolynomial graph diameter of
simple polytopes*.
-/

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

/-- The numerical layers used to drive the clock construction. -/
theorem Layer.numericalLayers : Layer.NumericalLayers :=
  Layer.numerical_of_primary Layer.primary

/-- The scheduler that supplies the clock and slack requests. -/
theorem scheduler : SchedulerTheorem :=
  Layer.scheduler_of_layers (Layer.layers_of_numerical Layer.numericalLayers)

/-- Simultaneous lower bounds for full and prescribed local crossings. -/
theorem finiteScale : FiniteScale := finiteScale_of_scheduler scheduler

/-- The crossing construction after capping, perturbation and rationalization. -/
theorem capped : CapLemma := cap_of_crossing finiteScale

/-- Theorem 1.1 with explicit vertices attaining the extreme objective values. -/
theorem main :
  ∀ moves : ℕ → ℕ, (∀ n, 0 < moves n) → Subpolynomial moves →
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        Simple poly.body ∧ (graph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (family n).poly.dist (moves n)
        (family n).obj.high (family n).obj.low) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ) ^ (-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ) ^ exponent ≤ (family n).poly.dist (moves n) first last := main_of_cap capped

/-- Theorem 1.1 with mathlib's undirected graph diameter. The objective and both
asymptotic bounds refer to the same family, chosen before the separation exponent. -/
theorem theorem_1_1 (moves : ℕ → ℕ) (positive : ∀ n, 0 < moves n) (sub : Subpolynomial moves) :
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        Simple poly.body ∧ (graph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (graph (family n).poly.body (moves n)).diam) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ)^(-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ)^exponent ≤ (family n).poly.dist (moves n) first last := by
  obtain ⟨F,hF,hd,hh,hs⟩ := main moves positive sub
  refine ⟨F,hF,hd,fun exponent => ?_,hs⟩
  filter_upwards [hF,hh exponent] with n hn hl
  have conn := hn.2.1.mono (graph_mono (F n).poly.body (positive n))
  exact hl.trans (Nat.cast_le.mpr (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp conn)))

/-- Ordinary undirected edge distance, at every sufficiently large facet count. -/
theorem superpolynomial_graph_diameter :
    ∃ family : ℕ → Polytope,
      (∀ᶠ n in atTop, Simple (family n).body ∧ (graph (family n).body 1).Connected ∧
        (family n).facetCount = n) ∧
      Subpolynomial (fun n => (family n).dimension) ∧
      Superpolynomial (fun n => (graph (family n).body 1).diam) := by
  have sub : Subpolynomial (fun _ => 1) := by
    intro eps he
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa using Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) he.le
  obtain ⟨F,hF,hd,hh,_⟩ := theorem_1_1 _ (fun _ => Nat.zero_lt_one) sub
  exact ⟨fun n => (F n).poly,hF,hd,hh⟩

/-- A single family eventually beats each polynomial with real coefficients. -/
theorem graph_diameter_beats_polynomials :
    ∃ family : ℕ → Polytope,
      (∀ᶠ n in atTop, Simple (family n).body ∧ (graph (family n).body 1).Connected ∧
        (family n).facetCount = n) ∧
      Subpolynomial (fun n => (family n).dimension) ∧
      ∀ p : Polynomial ℝ, ∀ᶠ n : ℕ in atTop, p.eval (n : ℝ) < (graph (family n).body 1).diam := by
  obtain ⟨F,hF,hd,hg⟩ := superpolynomial_graph_diameter
  refine ⟨F,hF,hd,fun p => ?_⟩
  let C := ∑ i ∈ Finset.range (p.natDegree+1), |p.coeff i|
  obtain ⟨m,hm⟩ := exists_nat_gt C
  filter_upwards [hg (p.natDegree+1 : ℕ),eventually_gt_atTop m] with n hn hlarge
  have hpos : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hC : C < (n : ℝ) := hm.trans (Nat.cast_lt.mpr hlarge)
  rw [Real.rpow_natCast,pow_succ'] at hn
  calc
    p.eval (n : ℝ) ≤ C * (n : ℝ)^p.natDegree := by
      rw [Polynomial.eval_eq_sum_range]; unfold C; rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ hpos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        (by positivity) (abs_nonneg _)
    _ < (n : ℝ) * (n : ℝ)^p.natDegree := mul_lt_mul_of_pos_right hC (by positivity)
    _ ≤ _ := hn

/-- No polynomial in the facet count bounds all vertex–edge distances, even
on bounded simple rational polytopes with connected graphs. -/
theorem not_polynomialHirsch :
  ¬ (∃ coeff power : ℕ, ∀ poly : Polytope, Simple poly.body → (graph poly.body 1).Connected →
    ∀ first last : poly.V, poly.dist 1 first last ≤ coeff * (poly.facetCount + 1) ^ power) := not_polynomialHirsch_of_main main

/-- Theorem 1.2 for prescribed dimension and facet excess. -/
theorem theorem_1_2 :
  ∀ a b : ℝ, 0 < a → 0 < b → ∃ c delta : ℝ, 0 < c ∧ 0 < delta ∧
    ∃ threshold : ℕ, ∀ d excess : ℕ, threshold ≤ min d excess →
      ∃ poly : Polytope, Simple poly.body ∧ (graph poly.body 1).Connected ∧
        poly.dimension = d ∧ poly.facetCount = d + excess ∧
        ∃ first last : poly.V,
          c * excess * min ((excess : ℝ) ^ a) ((d : ℝ) ^ b) ≤
            poly.dist ⌊((min d excess : ℕ) : ℝ) ^ delta⌋₊ first last := excess_of_cap capped

end OAI.Geometry.Hirsch
