import OAI.LinearAlgebra.SpectralBooks.ManyRelocationDepth
import OAI.LinearAlgebra.SpectralBooks.CubeTable.CubeCost

/-! # From finite exterior splits to a coupled relocation inequality

The number of rounds is fixed before taking large tensor powers. At each
coordinate its original transport bound controls every midpoint in the finite
tree. A selected path accumulates at most one slack per level, independently
for the interior and endpoint estimates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter
open scoped Topology
namespace CubeTable

variable {r : ℕ}

/-- Gap ranges contained in the prescribed wire-price bounds for every mark. -/
def AdmissibleGaps (g : Fin r → ℝ) (N : CubeTable r) : Prop :=
  ∀ i, -g i ≤ lower N i ∧ upper N i ≤ g i

theorem admissibleGaps_of_transport {g : Fin r → ℝ} {N : CubeTable r}
    (h : ∀ i x, |gap N i x| ≤ g i) : AdmissibleGaps g N :=
  fun i => ⟨lower_ge_of_forall _ _ (fun x => (abs_le.mp (h i x)).1),
    upper_le_of_forall _ _ (fun x => (abs_le.mp (h i x)).2)⟩

theorem AdmissibleGaps.child {g : Fin r → ℝ} {N : CubeTable r} (h : AdmissibleGaps g N)
    (i : Fin r) (b : Bool) : AdmissibleGaps g (child N i b) :=
  fun j => ⟨(h j).1.trans (lower_le_child N i j b), (upper_child_le N i j b).trans (h j).2⟩

theorem AdmissibleGaps.abs_midpoint_le {g : Fin r → ℝ} {N : CubeTable r}
    (h : AdmissibleGaps g N) (i : Fin r) : |midpoint N i| ≤ g i :=
  abs_le.mpr ⟨(h i).1.trans (midpoint_mem N i).1, (midpoint_mem N i).2.trans (h i).2⟩

/-- One-sided endpoint comparison of an actual node and its ideal table. -/
def EndpointBound (actual table : CubeTable r) (slack : ℝ) : Prop :=
  ∀ x, actual x ≤ table x + slack

/-- One geometric split selects a child whose interior price pays at most the
split error, including the cost of summing, and whose endpoint bounds pay at
most that error on top of their existing slack. -/
def SelectedSplit {X : Type*} (endpoint : X → CubeTable r) (inside : X → ℝ)
    (ε : ℝ) (N : CubeTable r) (i : Fin r) : Prop :=
  ∀ x σ, 0 ≤ σ → EndpointBound (endpoint x) N σ →
    ∃ y b, inside x ≤ inside y + ε ∧ EndpointBound (endpoint y) (child N i b) (σ + ε)

/-- Eliminate fixed-depth and power-normalization errors. The leaf functional
may be any endpoint estimate whose excess over `B` is bounded by the maximal
coordinate variation times `K`. In the coupling application `K = 2r`. -/
theorem root_le_of_selected_splits {X : ℕ → Type*} (endpoint : ∀ n, X n → CubeTable r)
    (inside : ∀ n, X n → ℝ) (root : ∀ n, X n) (M : CubeTable r) (g : Fin r → ℝ)
    {d B K : ℝ} (hM : AdmissibleGaps g M)
    (hroot : ∀ᶠ n : ℕ in atTop, d ≤ inside n (root n) ∧ endpoint n (root n) ≤ M)
    (step : ∀ ε > 0, ∀ N i, |midpoint N i| ≤ g i →
      ∀ᶠ n : ℕ in atTop, SelectedSplit (endpoint n) (inside n) ε N i)
    (leaf : ∀ᶠ n : ℕ in atTop, ∀ (y : X n) (N : CubeTable r) (σ ω : ℝ),
      N ≤ M → 0 ≤ ω → (∀ i, width N i ≤ ω) → EndpointBound (endpoint n y) N σ →
        inside n y ≤ B + K * ω + σ) : d ≤ B := by
  let W := ∑ i : Fin r, |width M i|
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw (i : Fin r) : width M i ≤ W :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (width M j)) (Finset.mem_univ i))
  apply relocation_width_limit (w := K * W)
  intro a
  let sites := ManyRelocation.rounds r a
  have he (ε : ℝ) (hε : 0 < ε) :
      d ≤ (B + K * W / 2 ^ a) + (2 * sites.length) * ε := by
    have hcheck := ManyRelocation.eventually_atEveryNode child
      (fun n => SelectedSplit (endpoint n) (inside n) ε) (AdmissibleGaps g)
      (fun _ i b h => h.child i b) (fun N i h => step ε hε N i (h.abs_midpoint_le i)) sites M hM
    obtain ⟨n, ⟨⟨hd, hR⟩, htree⟩, hleaf⟩ := ((hroot.and hcheck).and leaf).exists
    have hentry : EndpointBound (endpoint n (root n)) M 0 := fun x => by simpa using hR x
    obtain ⟨y, N, path, interior, bound⟩ := ManyRelocation.selectedLeaf child (inside n)
      (fun x => EndpointBound (endpoint n x)) _ hε.le
      (fun x N i σ ok hs hx => ok x σ hs hx) sites M (root n) le_rfl hentry htree
    have hNM := ManyRelocation.le_of_reaches child child_le path
    have hsmall (i : Fin r) : width N i ≤ W / 2 ^ a := by
      have h := ManyRelocation.width_at_leaf child width width_child
        (fun N j k b _ => width_child_le N j k b) path i
      simp only [sites, ManyRelocation.count_rounds] at h
      exact h.trans (div_le_div_of_nonneg_right (hw i) (by positivity))
    have hprice := hleaf y N _ (W / 2 ^ a) hNM (by positivity) hsmall bound
    simp only [zero_add] at interior bound hprice
    rw [← mul_div_assoc] at hprice
    linarith
  have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := (hzero.const_mul (2 * (sites.length : ℝ))).const_add (B + K * W / 2 ^ a)
  apply ge_of_tendsto' (by simpa using hlim)
  exact fun k => he _ (by positivity)

theorem IsCoupling.cost_le_of_endpointBound {π N M : CubeTable r} {t : Fin r → ℝ} {σ : ℝ}
    (hπ : IsCoupling π t) (h : EndpointBound N M σ) : cost π N ≤ cost π M + σ := by
  calc
    _ ≤ ∑ x, π x * (M x + σ) :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hπ.nonneg x)
    _ = _ := by simp [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ.total, cost]

/-- Independent relocation at each actual node, together with the exterior split
at every admissible midpoint, gives the root bound for every coupling of the
prescribed marginals. -/
theorem manySiteCoupledRelocation {X : ℕ → Type*} (endpoint : ∀ n, X n → CubeTable r)
    (inside : ∀ n, X n → ℝ) (root : ∀ n, X n) (M : CubeTable r) (g : Fin r → ℝ)
    {d : ℝ} (hM : AdmissibleGaps g M) {t : Fin r → ℝ} (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hroot : ∀ᶠ n : ℕ in atTop, d ≤ inside n (root n) ∧ endpoint n (root n) ≤ M)
    (step : ∀ ε > 0, ∀ N i, |midpoint N i| ≤ g i →
      ∀ᶠ n : ℕ in atTop, SelectedSplit (endpoint n) (inside n) ε N i)
    (hind : ∀ᶠ n : ℕ in atTop, ∀ y, inside n y ≤ cost (independent t) (endpoint n y))
    (π : CubeTable r) (hπ : IsCoupling π t) : d ≤ cost π M := by
  apply root_le_of_selected_splits endpoint inside root M g (K := 2 * r) hM hroot step
  filter_upwards [hind] with n hn
  intro y N σ ω hN hω hw hB
  have hprod := independent_isCoupling ht
  linarith [hn y, hprod.cost_le_of_endpointBound hB,
    cost_le_cost_of_width hprod hπ N hω hw, cost_mono hπ hN]

/-- All coordinates use the same Bernoulli outcome, including the case of no marks. -/
noncomputable def synchronized (r : ℕ) (t : ℝ) : CubeTable r := fun x =>
  (if (fun _ => false) = x then 1-t else 0) + (if (fun _ => true) = x then t else 0)

theorem synchronized_isCoupling {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    IsCoupling (synchronized r t) (fun _ => t) := by
  constructor
  · intro x
    unfold synchronized
    split_ifs <;> linarith [ht.1, ht.2]
  · simp [synchronized, Finset.sum_add_distrib]
  · intro i
    have hm (x : Fin r → Bool) : (if x i then synchronized r t x else 0) =
        if (fun _ => true) = x then t else 0 := by
      by_cases h0 : (fun _ => false) = x
      · subst x
        have hne : (fun _ : Fin r => true) ≠ (fun _ => false) :=
          fun h => Bool.noConfusion (congrFun h i)
        simp [hne]
      by_cases h1 : (fun _ => true) = x
      · subst x
        simp [synchronized, h0]
      simp [synchronized, h0, h1]
    simp [hm]

theorem cost_synchronized (t : ℝ) (M : CubeTable r) :
    cost (synchronized r t) M = (1-t) * M (fun _ => false) + t * M (fun _ => true) := by
  simp [cost, synchronized, add_mul, Finset.sum_add_distrib, ite_mul]

/-- The corresponding bound along synchronized geodesics. -/
theorem synchronized_of_forall_couplings {d t : ℝ} {M : CubeTable r}
    (ht : t ∈ Set.Icc 0 1)
    (h : ∀ π : CubeTable r, IsCoupling π (fun _ => t) → d ≤ cost π M) :
    d ≤ (1-t) * M (fun _ => false) + t * M (fun _ => true) := by
  simpa only [cost_synchronized] using h _ (synchronized_isCoupling ht)

end CubeTable

end SpectralBooks
end LinearAlgebra
end OAI
