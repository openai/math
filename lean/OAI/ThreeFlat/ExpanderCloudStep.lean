import OAI.ThreeFlat.ExpanderCloudGraph
import OAI.ThreeFlat.ExpanderCloudNumerator
import OAI.ThreeFlat.ExpanderCesaro

namespace OAI
/-! # One bounded-degree amplification step -/

namespace ThreeFlat.Expander

open Matrix Finset Computability.VPVNP.SpectralGeometry
open scoped BigOperators
universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Normalizing a regular arc table gives a row-stochastic matrix.
Symmetry also makes it column stochastic. -/
theorem transition_stochastic (c : V → V → ℕ) {b : ℕ} (hb : 0 < b)
    (hs : ∀ i j, c i j = c j i) (hr : ∀ i, ∑ j, c i j = b) :
    transition c b ∈ rowStochastic ℝ V ∧ transition c b ∈ colStochastic ℝ V := by
  have h (i : V) : ∑ j, transition c b i j = 1 := by
    simp only [transition, ← sum_div, ← Nat.cast_sum, hr]
    exact div_self (Nat.cast_ne_zero.mpr hb.ne')
  refine ⟨mem_rowStochastic_iff_sum.mpr ⟨fun i j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), h⟩,
    mem_colStochastic_iff_sum.mpr ⟨fun i j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩⟩
  intro j
  convert h j using 1
  exact sum_congr rfl fun i _ => congrArg (fun d : ℕ => (d : ℝ) / b) (hs i j)

/-- One graph replacement, including the walk denominators and the matching
realization. The new graph is chosen before the metric target. -/
theorem exists_cesaro_cloud_step [Nonempty V] {b h k q : ℕ}
    (hb : 0 < b) (hh : 0 < h) (hk : 0 < k) (hq : 0 < q)
    (hd : (2*k) * (2*b)^(2*k) ∣ q)
    (c : V → V → ℕ) (hs : ∀ i j, c i j = c j i) (hr : ∀ i, ∑ j, c i j = b)
    (H : Fin q → Fin q → ℕ) (hHs : ∀ i j, H i j = H j i) (hHr : ∀ i, ∑ j, H i j = h) :
    ∃ c' : (V × Fin q) → (V × Fin q) → ℕ,
      (∀ i j, c' i j = c' j i) ∧ (∀ i, ∑ j, c' i j = 2*h) ∧
      ∀ (Y : Type u) [PseudoMetricSpace Y] [CompleteSpace Y], HasCATZeroSegments Y →
        ∀ {β γ : ℝ}, 1 ≤ β → 0 ≤ γ →
          Bound (transition H h) Y β → Bound (transition c b) Y γ →
          Bound (transition c' (2*h)) Y (2*(6+18*(48*(1+γ/(2*(k:ℝ)))))*β) := by
  obtain ⟨a, has, har, heq⟩ := exists_cesaro_arc_table c hb (by omega) hq hs hr hd
  obtain ⟨g, hgs, hgr, bound⟩ := exists_cloud_graph.{u} hq hh a has har H hHs hHr
  obtain ⟨row, col⟩ := transition_stochastic c hb hs hr
  refine ⟨g, hgs, hgr, ?_⟩
  intro Y _ _ geom β γ hβ hγ inner old
  apply bound Y hβ (by positivity) inner
  rw [heq]
  exact bound_cesaro_lazy geom row col hγ old hk

end ThreeFlat.Expander

end OAI
