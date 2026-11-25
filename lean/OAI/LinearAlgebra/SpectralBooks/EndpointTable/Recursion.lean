import OAI.LinearAlgebra.SpectralBooks.Coupling
import OAI.LinearAlgebra.SpectralBooks.DepthLimit

/-! # Passing from exterior splits of finite wires to a coupled distance bound

At wire dimension `2^n` the root exponents have size `n`. The cost of
choosing a summand and the error in the two adjacent exterior dimensions
are bounded independently of `n`. Their total cost at a fixed depth thus
vanishes after division by `n`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace EndpointTable

open Filter
open scoped Topology

/-- Four endpoint distances of the two intervals. -/
def distances {X : Type*} [PseudoMetricSpace X] (A B : Fin 2 → X) : EndpointTable :=
  fun i j ↦ dist (A i) (B j)

theorem gapBound_distances {X : Type*} [PseudoMetricSpace X] (A B : Fin 2 → X) :
    GapBound (dist (A 0) (A 1)) (distances A B) := by
  intro j
  change |dist (A 0) (B j) - dist (A 1) (B j)| ≤ dist (A 0) (A 1)
  exact abs_dist_sub_le _ _ _

/-- The same gap bound applies directly to a spectral wire pseudodistance
before passing to its metric quotient. -/
theorem gapBound_of_triangle {X : Type*} (d : X → X → ℝ)
    (symm : ∀ x y, d x y = d y x) (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (A B : Fin 2 → X) : GapBound (d (A 0) (A 1)) (fun i j ↦ d (A i) (B j)) := by
  intro j
  change |d (A 0) (B j) - d (A 1) (B j)| ≤ d (A 0) (A 1)
  exact abs_le.mpr ⟨by linarith [triangle (A 1) (A 0) (B j), symm (A 0) (A 1)],
    by linarith [triangle (A 0) (A 1) (B j)]⟩

private theorem gap_smul (k : ℝ) (M : EndpointTable) (j : Fin 2) :
    gap (k • M) j = k * gap M j := by simp [gap, mul_sub]

private theorem width_smul {k : ℝ} (hk : 0 ≤ k) (M : EndpointTable) :
    width (k • M) = k * width M := by simp [width, gap_smul, ← mul_sub, abs_mul, abs_of_nonneg hk]

private theorem cost_smul (w M : EndpointTable) (k : ℝ) : cost w (k • M) = k * cost w M := by
  simp only [cost, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr! 2 with i _ j
  ring

private theorem gapBound_smul {t k : ℝ} {M : EndpointTable} (h : GapBound t M) (hk : 0 ≤ k) :
    GapBound (k*t) (k • M) := by
  intro j
  rw [gap_smul, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left (h j) hk

/-- The concrete finite split estimates for the two possible orderings of
the exterior operators. All exponents include the ancestor wire normalization. -/
def HasSplit {X : Type*} (endpoint : X → EndpointTable) (interior : X → ℝ) (t e : ℝ) : Prop :=
  ∀ x c, |c| ≤ t → ∃ y, interior x ≤ interior y + e ∧ endpoint y ≤ endpoint x ∧
    ((∀ j, endpoint y 0 j ≤ endpoint x 1 j + c + e) ∨
     (∀ j, endpoint y 1 j ≤ endpoint x 0 j - c + e))

/-- Finite-dimensional estimate obtained by following a largest-price
child at each step and keeping the exact ideal exponent table. -/
theorem HasSplit.finite_coupling_bound {X : Type*} {endpoint : X → EndpointTable} {interior : X → ℝ}
    {t e u v : ℝ} (split : HasSplit endpoint interior t e) (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) {π : EndpointTable} (hπ : IsCoupling π u v)
    (hind : ∀ x, interior x ≤ cost (independent u v) (endpoint x))
    (root : X) (M : EndpointTable) (hM : GapBound t M) (hroot : endpoint root ≤ M) (a : ℕ) :
    interior root ≤ cost π M + width M / 2^a + 2*a*e := by
  apply selectedPath_coupling_bound endpoint interior he hu hv π hπ hind _ root M hM hroot a
  intro x N σ hN _ hactual
  obtain ⟨y, hy, hweak, hstrong⟩ := split x N.midpoint hN.midpoint_le
  have hs (i j) : endpoint y i j ≤ endpoint x i j + e :=
    (hweak i j).trans (le_add_of_nonneg_right he)
  rcases hstrong with hp | hm
  · exact ⟨y, N.plus, Or.inl rfl, hy, boundedBy_plus hactual hs hp⟩
  · exact ⟨y, N.minus, Or.inr rfl, hy, boundedBy_minus hactual hs hm⟩

/-- Exact coupling from finite exterior splittings with dimension-independent
error. The index `n` is the base-two logarithm of wire dimension. -/
theorem coupling_of_exterior_splits {X : ℕ → Type*} (endpoint : ∀ n, X n → EndpointTable)
    (interior : ∀ n, X n → ℝ) {t e u v d : ℝ} (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1) {π : EndpointTable} (hπ : IsCoupling π u v)
    (M : EndpointTable) (hM : GapBound t M)
    (split : ∀ n : ℕ, 1 ≤ n → HasSplit (endpoint n) (interior n) (n*t) e)
    (hind : ∀ n : ℕ, 1 ≤ n → ∀ x, interior n x ≤ cost (independent u v) (endpoint n x))
    (hroot : ∀ n : ℕ, 1 ≤ n → ∃ x, n*d ≤ interior n x ∧ endpoint n x ≤ (n : ℝ) • M) :
    d ≤ cost π M := by
  apply relocation_width_limit (w := width M)
  intro a
  have herr : Tendsto (fun n : ℕ ↦ 2*(a:ℝ)*e/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply ge_of_tendsto (by simpa using herr.const_add (cost π M + width M / 2^a))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  obtain ⟨x, hx, htab⟩ := hroot n hn
  have h := hx.trans ((split n hn).finite_coupling_bound he hu hv hπ (hind n hn) x _
    (gapBound_smul hM hn'.le) htab a)
  rw [cost_smul, width_smul hn'.le] at h
  have h' : (n:ℝ) * (d - (cost π M + width M / 2^a)) ≤ 2*a*e := by
    rw [mul_sub, mul_add, ← mul_div_assoc]
    linarith only [h]
  have h'' : d - (cost π M + width M / 2^a) ≤ 2*(a:ℝ)*e/n :=
    (le_div_iff₀ hn').mpr (by simpa [mul_comm] using h')
  linarith only [h'']

/-- Synchronized endpoint transport is the diagonal choice of coupling. -/
theorem synchronized_of_exterior_splits {X : ℕ → Type*} (endpoint : ∀ n, X n → EndpointTable)
    (interior : ∀ n, X n → ℝ) {t e u d : ℝ} (he : 0 ≤ e)
    (hu : u ∈ Set.Icc 0 1) (M : EndpointTable) (hM : GapBound t M)
    (split : ∀ n : ℕ, 1 ≤ n → HasSplit (endpoint n) (interior n) (n*t) e)
    (hind : ∀ n : ℕ, 1 ≤ n → ∀ x, interior n x ≤ cost (independent u u) (endpoint n x))
    (hroot : ∀ n : ℕ, 1 ≤ n → ∃ x, n*d ≤ interior n x ∧ endpoint n x ≤ (n : ℝ) • M) :
    d ≤ (1-u) * M 0 0 + u * M 1 1 := by
  simpa only [cost_synchronized] using coupling_of_exterior_splits endpoint interior he hu hu
    (synchronized_isCoupling hu) M hM split hind hroot

end EndpointTable

end SpectralBooks
end LinearAlgebra
end OAI
