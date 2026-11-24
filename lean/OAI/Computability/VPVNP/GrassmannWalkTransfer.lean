import OAI.Computability.VPVNP.GrassmannTypes
import OAI.Computability.VPVNP.SparseGrassmann

/-!
# Passing the strict Grassmann inequality to a sparse walk

Average the strict Grassmann inequality over the random linear map. The two
marginal laws needed here are independence on complementary planes and
independence within matching fibers on adjacent planes. All averages are
finite sums. The vertex factor in the conclusion agrees with the walk energy
normalization in Section 5.2.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open SpectralGeometry

variable {Ω I E S X : Type*} [Fintype Ω] [Fintype I] [Fintype E] [Fintype S]

/-- Uniform expectation over a finite sample space. -/
noncomputable def expectation {T : Type*} [Fintype T] (f : T → ℝ) : ℝ :=
  (∑ t, f t) / Fintype.card T

private theorem expectation_swap {T : Type*} [Fintype T] (f : S → T → ℝ) :
    expectation (fun s ↦ expectation (f s)) = expectation (fun t ↦ expectation (fun s ↦ f s t)) := by
  unfold expectation
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

private theorem expectation_const {T : Type*} [Fintype T] [Nonempty T] (v : ℝ) :
    expectation (fun _ : T ↦ v) = v := by
  simp [expectation, Fintype.card_ne_zero]

private theorem expectation_div {T : Type*} [Fintype T] (f : T → ℝ) (c : ℝ) :
    expectation (fun t ↦ f t / c) = expectation f / c := by
  unfold expectation
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

/-- The two finite marginal distributions of the linear-map sampling experiment.
Each equation quantifies over all observables, independently of the metric target. -/
structure PairSamplingLaws {m : ℕ} (sample : S → Plane m → Ω)
    (l r : Pair m 1 → I × E ≃ Ω) : Prop where
  complementary : ∀ (p : Pair m m) (g : Ω → Ω → ℝ),
    expectation (fun s ↦ g (sample s p.val.1) (sample s p.val.2)) =
      (∑ u, ∑ v, g u v) / (Fintype.card Ω : ℝ) ^ 2
  adjacent : ∀ (p : Pair m 1) (g : Ω → Ω → ℝ),
    expectation (fun s ↦ g (sample s p.val.1) (sample s p.val.2)) =
      ((∑ i, ∑ a, ∑ b, g (l p (i,a)) (r p (i,b))) / Fintype.card E) / Fintype.card Ω

variable [PseudoMetricSpace X] {m : ℕ}

/-- Average a Grassmann inequality over the sample space and use the pair
laws to identify its left side with the uniform all-pairs energy. -/
theorem PairSamplingLaws.transfer [Nonempty Ω] [Nonempty (Pair m m)]
    {sample : S → Plane m → Ω} {l r : Pair m 1 → I × E ≃ Ω}
    (hs : PairSamplingLaws sample l r) {c : ℝ}
    (hgrass : ∀ f : Plane m → X,
      mean (fun a b ↦ dist (f a) (f b) ^ 2) m ≤ c * mean (fun a b ↦ dist (f a) (f b) ^ 2) 1)
    (x : Ω → X) :
    (∑ u, ∑ v, dist (x u) (x v) ^ 2) / Fintype.card Ω ≤
      c * ((∑ p, adjacentEnergy (l p) (r p) x) / Fintype.card (Pair m 1)) := by
  let g (u v : Ω) := dist (x u) (x v) ^ 2
  let pairFn (d : ℕ) (s : S) (p : Pair m d) := g (sample s p.val.1) (sample s p.val.2)
  have point (s : S) : expectation (pairFn m s) ≤ c * expectation (pairFn 1 s) :=
    hgrass (fun U ↦ x (sample s U))
  have averaged : expectation (fun s ↦ expectation (pairFn m s)) ≤
      c * expectation (fun s ↦ expectation (pairFn 1 s)) := by
    have h := div_le_div_of_nonneg_right (Finset.sum_le_sum (s := Finset.univ) fun s _ ↦ point s)
      (Nat.cast_nonneg (α := ℝ) (Fintype.card S))
    simpa only [expectation, ← Finset.mul_sum, mul_div_assoc] using h
  rw [expectation_swap (pairFn m), expectation_swap (pairFn 1)] at averaged
  have hm (p : Pair m m) : expectation (fun s ↦ pairFn m s p) = (∑ u, ∑ v, g u v) /
      (Fintype.card Ω : ℝ) ^ 2 := hs.complementary p g
  have h₁ (p : Pair m 1) : expectation (fun s ↦ pairFn 1 s p) =
      adjacentEnergy (l p) (r p) x / Fintype.card Ω := hs.adjacent p g
  simp only [hm, expectation_const, h₁, expectation_div] at averaged
  have ho : 0 < (Fintype.card Ω : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h := mul_le_mul_of_nonneg_right averaged ho.le
  have hcancel (y : ℝ) : y / (Fintype.card Ω : ℝ) ^ 2 * Fintype.card Ω =
      y / Fintype.card Ω := by field_simp
  rw [hcancel, mul_assoc, div_mul_cancel₀ _ ho.ne'] at h
  exact h

/-- Given the marginal laws of the random linear map, the actual fiber and
permutation mixture has the recursive Poincaré coefficient of Section 5.2. -/
theorem PairSamplingLaws.sparseBound [Nonempty Ω] [Nonempty E]
    [Nonempty (Pair m 1)] [Nonempty (Pair m m)]
    {sample : S → Plane m → Ω} {l r : Pair m 1 → I × E ≃ Ω}
    (hs : PairSamplingLaws sample l r) (P : Matrix E E ℝ) {ε γ c : ℝ}
    (hε : 0 < ε) (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hP : HasPoincareBound X P γ)
    (hgrass : ∀ f : Plane m → X,
      mean (fun a b ↦ dist (f a) (f b) ^ 2) m ≤ c * mean (fun a b ↦ dist (f a) (f b) ^ 2) 1) :
    HasPoincareBound X (sparseWalk l r P ((1 + ε) * γ) (1 + 1 / ε))
      (c * ((1 + ε) * γ + (1 + 1 / ε))) :=
  sparseWalk_hasPoincareBound l r P hε hγ hc hP (hs.transfer hgrass)

end Grassmann

end VPVNP
end Computability
end OAI
