import OAI.ThreeFlat.ExpanderBasic

namespace OAI
/-! # Relabeling expander vertices and the uniform initial kernel -/

noncomputable section
namespace ThreeFlat.Expander

open Finset Matrix
open scoped Classical

variable {V W X : Type*}

/-- Transport both indices of a transition matrix along a vertex equivalence. -/
def reindexKernel (e : V ≃ W) (G : Matrix V V ℝ) : Matrix W W ℝ :=
  G.reindex e e

@[simp] theorem reindexKernel_apply (e : V ≃ W) (G : Matrix V V ℝ) (i j : W) :
    reindexKernel e G i j = G (e.symm i) (e.symm j) := rfl

theorem reindexKernel_symmetric (e : V ≃ W) {G : Matrix V V ℝ}
    (hsym : ∀ i j, G i j = G j i) (i j : W) :
    reindexKernel e G i j = reindexKernel e G j i :=
  hsym _ _

variable [Fintype V] [Fintype W]

theorem reindexKernel_row [DecidableEq V] [DecidableEq W] (e : V ≃ W)
    {G : Matrix V V ℝ} (hG : G ∈ rowStochastic ℝ V) :
    reindexKernel e G ∈ rowStochastic ℝ W :=
  reindex_mem_rowStochastic hG

theorem card_support_reindexKernel (e : V ≃ W) (G : Matrix V V ℝ) (i : W) :
    (univ.filter fun j => reindexKernel e G i j ≠ 0).card =
      (univ.filter fun j => G (e.symm i) j ≠ 0).card := by
  let s := univ.filter fun j => G (e.symm i) j ≠ 0
  have hsets : s.map e.toEmbedding = univ.filter (fun j => reindexKernel e G i j ≠ 0) := by
    apply Finset.ext
    intro j
    rw [mem_map_equiv]
    constructor
    · intro hj
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    · intro hj
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
  rw [← hsets, card_map]

variable [PseudoMetricSpace X]

theorem variance_comp_equiv (e : V ≃ W) (x : W → X) : variance (x ∘ e) = variance x := by
  calc
    _ = avg ((fun i => avg (fun j => dist (x i) (x j)^2)) ∘ e) := by
      apply avg_congr
      intro i
      exact avg_equiv e (fun j => dist (x (e i)) (x j)^2)
    _ = _ := avg_equiv e _

theorem energy_comp_equiv (e : V ≃ W) (G : Matrix V V ℝ) (x : W → X) :
    energy G (x ∘ e) = energy (reindexKernel e G) x := by
  calc
    _ = avg ((fun i => ∑ j, reindexKernel e G i j * dist (x i) (x j)^2) ∘ e) := by
      apply avg_congr
      intro i
      simpa only [Function.comp_apply, reindexKernel_apply, Equiv.symm_apply_apply] using
        e.sum_comp (fun j => reindexKernel e G (e i) j * dist (x (e i)) (x j)^2)
    _ = _ := avg_equiv e _

theorem Bound.reindexKernel {G : Matrix V V ℝ} {γ : ℝ} (hb : Bound G X γ)
    (e : V ≃ W) : Bound (Expander.reindexKernel e G) X γ := by
  intro x
  simpa only [variance_comp_equiv, energy_comp_equiv] using hb (x ∘ e)

/-- Each starting vertex chooses its next vertex independently and uniformly. -/
def uniformKernel (V : Type*) [Fintype V] : Matrix V V ℝ :=
  fun _ _ => 1 / Fintype.card V

theorem uniformKernel_symmetric (i j : V) : uniformKernel V i j = uniformKernel V j i := rfl

theorem uniformKernel_row (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    uniformKernel V ∈ rowStochastic ℝ V := by
  apply mem_rowStochastic_iff_sum.2
  refine ⟨fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _), ?_⟩
  intro i
  have h : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [uniformKernel, h]

theorem energy_uniformKernel (x : V → X) : energy (uniformKernel V) x = variance x := by
  apply avg_congr
  intro i
  simp only [uniformKernel, ← mul_sum, avg, div_eq_mul_inv, one_mul]
  exact mul_comm _ _

theorem bound_uniformKernel (V X : Type*) [Fintype V] [PseudoMetricSpace X] :
    Bound (uniformKernel V) X 1 := by
  intro x
  rw [energy_uniformKernel, one_mul]

end ThreeFlat.Expander

end
end OAI
