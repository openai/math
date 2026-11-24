import OAI.Computability.VPVNP.Barycenter
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Barycentric smoothing of a finite walk

Section 5.3 of *VP and VNP differ over every field* bounds the squared-distance
Poincaré constant of the Cesàro average of powers of a lazy walk. All energies
here multiply the paper's averages by the number of vertices. This common
factor cancels in the Poincaré inequality.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

/-- Sum of squared lengths over the directed edges with the given weights. -/
noncomputable def walkEnergy (A : Matrix ι ι ℝ) (x : ι → X) : ℝ :=
  ∑ i, ∑ j, A i j * dist (x j) (x i) ^ 2

/-- Row `i`'s mean squared distance from the previous configuration to its new center. -/
noncomputable def rowVariance (A : Matrix ι ι ℝ) (x : ℕ → ι → X) (h : ℕ) (i : ι) : ℝ :=
  ∑ j, A i j * dist (x h j) (x (h + 1) i) ^ 2

private noncomputable def accumulatedVariance (A : Matrix ι ι ℝ) (x : ℕ → ι → X) : ℕ → ι → ℝ
  | 0, _ => 0
  | h + 1, i => rowVariance A x h i + ∑ j, A i j * accumulatedVariance A x h j

private theorem variance_row_le (A : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (x : ℕ → ι → X)
    (hvar : ∀ h i z, rowVariance A x h i + dist (x (h + 1) i) z ^ 2 ≤
      ∑ j, A i j * dist (x h j) z ^ 2)
    (h : ℕ) (i : ι) (z : X) :
    accumulatedVariance A x h i + dist (x h i) z ^ 2 ≤
      ∑ j, (A ^ h) i j * dist (x 0 j) z ^ 2 := by
  induction h generalizing i with
  | zero => simp [accumulatedVariance, Matrix.one_apply, ite_mul]
  | succ h ih =>
    have hprev := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦
      mul_le_mul_of_nonneg_left (ih j) (hn i j)
    simp_rw [mul_add, Finset.sum_add_distrib] at hprev
    have hrew : (∑ j, A i j * ∑ k, (A ^ h) j k * dist (x 0 k) z ^ 2) =
        ∑ k, (A ^ (h + 1)) i k * dist (x 0 k) z ^ 2 := by
      rw [pow_succ']
      simp_rw [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [hrew] at hprev
    unfold accumulatedVariance
    linarith only [hvar h i z, hprev]

omit [DecidableEq ι] in
private theorem sum_accumulatedVariance (A : Matrix ι ι ℝ) (hcol : ∀ j, ∑ i, A i j = 1)
    (x : ℕ → ι → X) (h : ℕ) :
    ∑ i, accumulatedVariance A x h i = ∑ g ∈ Finset.range h, ∑ i, rowVariance A x g i := by
  induction h with
  | zero => simp [accumulatedVariance]
  | succ h ih =>
    simp only [accumulatedVariance, Finset.sum_add_distrib, Finset.sum_range_succ]
    rw [Finset.sum_comm (f := fun i j ↦ A i j * accumulatedVariance A x h j)]
    simp_rw [← Finset.sum_mul, hcol, one_mul]
    rw [ih, add_comm]

/-- Repeated conditioning using the variance inequality in each row. The edge
energy of an `h`-step stationary walk pays for the displacement of its barycentric
iterate and for all the intermediate row variances (Section 5.3, page 18). -/
theorem walkEnergy_ge_variances (A : Matrix ι ι ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (hcol : ∀ j, ∑ i, A i j = 1) (x : ℕ → ι → X)
    (hvar : ∀ h i z, rowVariance A x h i + dist (x (h + 1) i) z ^ 2 ≤
      ∑ j, A i j * dist (x h j) z ^ 2) (h : ℕ) :
    (∑ i, dist (x h i) (x 0 i) ^ 2) + (∑ g ∈ Finset.range h, ∑ i, rowVariance A x g i) ≤
      walkEnergy (A ^ h) (x 0) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    variance_row_le A hn x hvar h i (x 0 i)
  rwa [Finset.sum_add_distrib, sum_accumulatedVariance A hcol, add_comm] at hb

/-- Comparison through each row's center for the lazy stochastic matrix in §5.3. -/
theorem walkEnergy_le_four_localEnergy (P : Matrix ι ι ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (y b : ι → X) :
    (∑ i, ∑ j, P i j * dist (y i) (y j) ^ 2) ≤
      4 * ∑ i, ∑ j, (((if i = j then 1 else 0) + P i j) / 2) *
        dist (b i) (y j) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have triangle (j : ι) :
      dist (y i) (y j) ^ 2 ≤ 2 * (dist (b i) (y i) ^ 2 + dist (b i) (y j) ^ 2) := by
    have h := dist_triangle (y i) (b i) (y j)
    rw [dist_comm (y i) (b i)] at h
    have hs := pow_le_pow_left₀ dist_nonneg h 2
    nlinarith [sq_nonneg (dist (b i) (y i) - dist (b i) (y j))]
  calc
    _ ≤ ∑ j, P i j * (2 * (dist (b i) (y i) ^ 2 + dist (b i) (y j) ^ 2)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (triangle j) (hP i j)
    _ = 2 * (dist (b i) (y i) ^ 2 + ∑ j, P i j * dist (b i) (y j) ^ 2) := by
      simp_rw [show ∀ j, P i j * (2 * (dist (b i) (y i) ^ 2 + dist (b i) (y j) ^ 2)) =
        2 * (P i j * dist (b i) (y i) ^ 2 + P i j * dist (b i) (y j) ^ 2) by
          intro j; ring]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hrow, one_mul]
    _ = _ := by
      rw [Finset.mul_sum]
      simp_rw [show ∀ j, 4 * (((if i = j then 1 else 0) + P i j) / 2 *
          dist (b i) (y j) ^ 2) = 2 * ((if i = j then dist (b i) (y j) ^ 2 else 0) +
          P i j * dist (b i) (y j) ^ 2) by intro j; split_ifs <;> ring]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp

omit [DecidableEq ι] in
/-- Comparison of pairwise squared distances through an intermediate configuration in §5.3. -/
theorem pairVariance_le_displacement_variance (x y : ι → X) :
    (∑ i, ∑ j, dist (x i) (x j) ^ 2) ≤
      3 * (2 * (Fintype.card ι : ℝ) * (∑ i, dist (x i) (y i) ^ 2) +
        ∑ i, ∑ j, dist (y i) (y j) ^ 2) := by
  have pointwise (i j : ι) :
      dist (x i) (x j) ^ 2 ≤ 3 * (dist (x i) (y i) ^ 2 + dist (x j) (y j) ^ 2 +
        dist (y i) (y j) ^ 2) := by
    have h₁ := dist_triangle (x i) (y i) (x j)
    have h₂ := dist_triangle (y i) (y j) (x j)
    rw [dist_comm (y j) (x j)] at h₂
    have h := pow_le_pow_left₀ dist_nonneg (h₁.trans (add_le_add_right h₂ _)) 2
    nlinarith [sq_nonneg (dist (x i) (y i) - dist (x j) (y j)),
      sq_nonneg (dist (x i) (y i) - dist (y i) (y j)),
      sq_nonneg (dist (x j) (y j) - dist (y i) (y j))]
  calc
    _ ≤ ∑ i, ∑ j, 3 * (dist (x i) (y i) ^ 2 + dist (x j) (y j) ^ 2 +
        dist (y i) (y j) ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pointwise i j
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring

/-- Index selection in the CAT(0) walk averaging argument of Section 5.3.
The first half of the walk lengths pays for all the displacements. Each walk
in the second half pays for every energy in the first half. -/
theorem exists_walk_energy_le_average {n : ℕ} (hn : 0 < n) (D E W : ℕ → ℝ)
    (hD : ∀ g, 0 ≤ D g) (hE : ∀ g, 0 ≤ E g) (hzero : D 0 = 0)
    (hwalk : ∀ h, D (h + 1) + ∑ k ∈ Finset.range (h + 1), E k ≤ W (h + 1)) :
    ∃ g < n, D g + (n : ℝ) * E g ≤
      (∑ h ∈ Finset.range (2 * n), W (h + 1)) / n := by
  have hshift := Finset.sum_range_succ' D n
  rw [Finset.sum_range_succ, hzero, add_zero] at hshift
  have hnext : ∑ g ∈ Finset.range n, D (g + 1) ≤ ∑ g ∈ Finset.range n, W (g + 1) := by
    apply Finset.sum_le_sum
    intro g _
    linarith only [hwalk g, Finset.sum_nonneg (s := Finset.range (g + 1)) (fun k _ ↦ hE k)]
  have hfirst : ∑ g ∈ Finset.range n, D g ≤ ∑ g ∈ Finset.range n, W (g + 1) := by
    linarith only [hshift, hnext, hD n]
  have henergy (g : ℕ) : ∑ k ∈ Finset.range n, E k ≤ W (n + g + 1) := by
    have hsub : ∑ k ∈ Finset.range n, E k ≤ ∑ k ∈ Finset.range (n + g + 1), E k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun k _ _ ↦ hE k)
    linarith only [hsub, hwalk (n + g), hD (n + g + 1)]
  have hsecond : (n : ℝ) * (∑ k ∈ Finset.range n, E k) ≤
      ∑ g ∈ Finset.range n, W (n + g + 1) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.range n) (fun g _ ↦ henergy g))
  let total := ∑ h ∈ Finset.range (2 * n), W (h + 1)
  have hsum : ∑ g ∈ Finset.range n, (D g + (n : ℝ) * E g) ≤ total := by
    dsimp only [total]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, two_mul,
      Finset.sum_range_add (fun h ↦ W (h + 1)) n n]
    exact add_le_add hfirst hsecond
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmean : ∑ _g ∈ Finset.range n, total / n = total := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn'.ne']
  obtain ⟨g, hg, h⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr hn.ne')
    (hsum.trans_eq hmean.symm)
  exact ⟨g, Finset.mem_range.mp hg, h⟩

/-- The scalar estimate converting the selected walk bound to the amplified
Poincaré coefficient `max 12 (48 * γ / t)` in Section 5.3. -/
theorem walk_poincare_coefficient {D E S t γ : ℝ} (ht : 0 < t) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmean : D + (t / 2) * E ≤ 2 * S) :
    3 * (2 * D + 4 * γ * E) ≤ max 12 (48 * γ / t) * S := by
  let M := max 12 (48 * γ / t)
  have hleft : 12 ≤ M := le_max_left _ _
  have hright : 48 * γ ≤ M * t := (div_le_iff₀ ht).mp (le_max_right _ _)
  calc
    3 * (2 * D + 4 * γ * E) = 6 * D + (12 * γ) * E := by ring
    _ ≤ (M / 2) * D + (M * t / 4) * E :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith only [hleft]) hD)
        (mul_le_mul_of_nonneg_right (by linarith only [hright]) hE)
    _ = (M / 2) * (D + (t / 2) * E) := by ring
    _ ≤ (M / 2) * (2 * S) := mul_le_mul_of_nonneg_left hmean (by linarith only [hleft])
    _ = M * S := by ring

/-- Poincaré inequality in the normalization obtained by multiplying the paper's
variance and edge energy by the order of the graph. -/
def HasPoincareBound (X : Type*) [PseudoMetricSpace X] (A : Matrix ι ι ℝ) (γ : ℝ) : Prop :=
  ∀ x : ι → X, (∑ i, ∑ j, dist (x i) (x j) ^ 2) / Fintype.card ι ≤ γ * walkEnergy A x

/-- Add a one-half probability of staying at the current vertex. -/
noncomputable def lazyWalk (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ ((if i = j then 1 else 0) + P i j) / 2

/-- Uniform mixture of lengths from one to `t`, inclusive. -/
noncomputable def cesaroWalk (A : Matrix ι ι ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  fun i j ↦ (∑ h ∈ Finset.range t, (A ^ (h + 1)) i j) / t

private theorem walkEnergy_cesaro (A : Matrix ι ι ℝ) (t : ℕ) (x : ι → X) :
    walkEnergy (cesaroWalk A t) x = (∑ h ∈ Finset.range t, walkEnergy (A ^ (h + 1)) x) / t := by
  unfold walkEnergy cesaroWalk
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ i, ∑ h ∈ Finset.range t, ∑ j, (A ^ (h + 1)) i j * dist (x j) (x i) ^ 2 :=
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The averaging estimate in Section 5.3. The Cesàro average of the first `2n`
lazy powers has a Poincaré bound independent of `γ` once the number of powers
is proportional to `γ`. Symmetry of the original matrix may be replaced by
stationarity of the uniform measure, expressed by its column sums. -/
theorem cesaroWalk_hasPoincareBound [Nonempty ι] [CompleteSpace X] [Nonempty X]
    (hcat : HasCATZeroSegments X) (P : Matrix ι ι ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (hcol : ∀ j, ∑ i, P i j = 1)
    {γ : ℝ} (hγ : 0 ≤ γ) (hbound : HasPoincareBound X P γ) {n : ℕ} (hn : 0 < n) :
    HasPoincareBound X (cesaroWalk (lazyWalk P) (2 * n)) (max 12 (48 * γ / (2 * n))) := by
  let A := lazyWalk P
  have ha (i j : ι) : 0 ≤ A i j := by
    unfold A lazyWalk
    split_ifs <;> linarith only [hP i j]
  have harow (i : ι) : ∑ j, A i j = 1 := by
    simp [A, lazyWalk, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, hrow]
    norm_num
  have hacol (j : ι) : ∑ i, A i j = 1 := by
    simp [A, lazyWalk, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib, hcol]
    norm_num
  choose center hc using fun (p : ι → X) (i : ι) ↦
    exists_barycenter_variance hcat (A i) p (ha i) (harow i)
  intro x₀
  let x : ℕ → ι → X := fun k ↦ Nat.rec x₀ (fun _ p ↦ center p) k
  have hvar (g : ℕ) (i : ι) (z : X) : rowVariance A x g i + dist (x (g+1) i) z ^ 2 ≤
      ∑ j, A i j * dist (x g j) z ^ 2 := hc (x g) i z
  let D (g : ℕ) := ∑ i, dist (x g i) (x 0 i) ^ 2
  let E (g : ℕ) := ∑ i, rowVariance A x g i
  let W (h : ℕ) := walkEnergy (A ^ h) (x 0)
  have hD (g : ℕ) : 0 ≤ D g := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hE (g : ℕ) : 0 ≤ E g := Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (ha i j) (sq_nonneg _)
  have hDzero : D 0 = 0 := by simp [D]
  obtain ⟨g, _, hmean⟩ := exists_walk_energy_le_average hn D E W hD hE hDzero
    (fun h ↦ walkEnergy_ge_variances A ha hacol x hvar (h+1))
  have hlocal : walkEnergy P (x g) ≤ 4 * E g := by
    simpa only [walkEnergy, E, rowVariance, A, lazyWalk, dist_comm] using
      walkEnergy_le_four_localEnergy P hP hrow (x g) (x (g+1))
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnext := pairVariance_le_displacement_variance (x 0) (x g)
  simp only [dist_comm (x 0 _) (x g _)] at hnext
  have hratio : (∑ i, ∑ j, dist (x 0 i) (x 0 j) ^ 2) / Fintype.card ι ≤
      3 * (2 * D g + 4 * γ * E g) := by
    apply (div_le_iff₀ hcard).mpr
    have hmid := (div_le_iff₀ hcard).mp (hbound (x g))
    have hres := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlocal hγ) hcard.le
    dsimp only [D]
    linarith only [hnext, hmid, hres]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hpay : D g + (2 * (n : ℝ) / 2) * E g ≤ 2 * walkEnergy (cesaroWalk A (2*n)) (x 0) := by
    rw [walkEnergy_cesaro]
    push_cast
    change D g + 2 * (n : ℝ) / 2 * E g ≤ 2 * ((∑ h ∈ Finset.range (2 * n), W (h + 1)) / (2 * n))
    convert hmean using 1 <;> ring
  exact hratio.trans (walk_poincare_coefficient (by positivity : 0 < 2 * (n : ℝ))
    (hD g) (hE g) hpay)

end SpectralGeometry

end VPVNP
end Computability
end OAI
