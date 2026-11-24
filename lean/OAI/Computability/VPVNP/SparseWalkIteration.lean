import OAI.Computability.VPVNP.GrassmannWalkTransfer

/-!
# Iterating and rounding the sparse walk

The size `D` of the starting walk is a power of two. At each step the vertex
set consists of `m`-tuples of the preceding vertices. The row support grows by
at most a factor twice the number of Grassmann adjacencies, while the Poincaré
coefficient satisfies an affine recurrence with multiplier strictly below `m`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

universe u v

variable {T : Type u} (X : T → Type v) [∀ t, PseudoMetricSpace (X t)]
variable {E Ω : Type*} [Fintype E] [Fintype Ω]

/-- Uniform bounds for one symmetric stochastic matrix on every target in the class. -/
structure SparseWalkBound (P : Matrix E E ℝ) (k : ℕ) (γ : ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  row : ∀ i, ∑ j, P i j = 1
  symm : ∀ i j, P i j = P j i
  support : ∀ i, (rowSupport P i).card ≤ k
  bound : ∀ t, HasPoincareBound (X t) P γ

variable {X}

theorem SparseWalkBound.reindex {P : Matrix E E ℝ} {k : ℕ} {γ : ℝ}
    (h : SparseWalkBound X P k γ) (e : E ≃ Ω) :
    SparseWalkBound X (fun i j ↦ P (e.symm i) (e.symm j)) k γ := by
  classical
  let Q : Matrix Ω Ω ℝ := fun i j ↦ P (e.symm i) (e.symm j)
  change SparseWalkBound X Q k γ
  refine ⟨fun i j ↦ h.nonneg _ _, fun i ↦ ?_, fun i j ↦ h.symm _ _, fun i ↦ ?_, fun t x ↦ ?_⟩
  · exact (e.symm.sum_comp _).trans (h.row _)
  · have hs : rowSupport Q i ⊆ (rowSupport P (e.symm i)).image e := by
      intro j hj
      exact Finset.mem_image.mpr ⟨e.symm j, (mem_rowSupport _ _ _).mpr ((mem_rowSupport Q i j).mp hj),
        e.apply_symm_apply j⟩
    exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (h.support _))
  · have changeSum (f : Ω → Ω → ℝ) : (∑ i, ∑ j, f i j) = ∑ i, ∑ j, f (e i) (e j) := by
      rw [← e.sum_comp (fun i ↦ ∑ j, f i j)]
      exact Finset.sum_congr rfl fun i _ ↦ (e.sum_comp _).symm
    rw [changeSum, ← Fintype.card_congr e, walkEnergy, changeSum]
    simpa only [Q, Equiv.symm_apply_apply, walkEnergy, Function.comp_apply] using h.bound t (x ∘ e)

/-- The starting graph is the uniform matrix on the full set. -/
theorem uniform_sparseWalkBound (X : T → Type v) [∀ t, PseudoMetricSpace (X t)]
    (E : Type*) [Fintype E] [Nonempty E] :
    SparseWalkBound X (fun (_ _ : E) ↦ 1 / (Fintype.card E : ℝ)) (Fintype.card E) 1 := by
  have he : 0 < (Fintype.card E : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun _ _ ↦ by positivity, fun _ ↦ ?_, fun _ _ ↦ rfl,
    fun _ ↦ Finset.card_le_univ _, fun t x ↦ ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · unfold walkEnergy
    rw [one_mul]
    simp only [← Finset.mul_sum, div_eq_inv_mul, mul_one]
    rw [Finset.sum_comm (f := fun i j ↦ dist (x j) (x i) ^ 2)]

/-- Binary words of length `k`, used as the vertex vector space at each stage. -/
abbrev WordSpace (k : ℕ) := Fin k → ZMod 2

theorem card_wordSpace (k : ℕ) : Fintype.card (WordSpace k) = 2 ^ k := by
  simp [WordSpace, ZMod.card]

/-- The affine Poincaré recurrence in Section 5.2. -/
def sparseCoefficient (α κ : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => α * sparseCoefficient α κ j + κ

theorem sparseCoefficient_nonneg {α κ : ℝ} (ha : 0 ≤ α) (hk : 0 ≤ κ) (j : ℕ) :
    0 ≤ sparseCoefficient α κ j := by
  induction j with
  | zero => exact zero_le_one
  | succ j ih => exact add_nonneg (mul_nonneg ha ih) hk

/-- Solving the recurrence gives a prefactor independent of the starting size
and the iteration index. -/
theorem sparseCoefficient_le {α κ : ℝ} (ha : 1 < α) (hk : 0 ≤ κ) (j : ℕ) :
    sparseCoefficient α κ j ≤ (1 + κ / (α - 1)) * α ^ j := by
  have hdiv := div_nonneg hk (sub_nonneg.mpr ha.le)
  have hshift : α * (κ / (α - 1)) = κ / (α - 1) + κ := by field_simp [(sub_pos.mpr ha).ne']; ring
  have heq : sparseCoefficient α κ j + κ / (α - 1) = (1 + κ / (α - 1)) * α ^ j := by
    induction j with
    | zero => simp [sparseCoefficient]
    | succ j ih =>
      rw [sparseCoefficient, pow_succ', ← mul_assoc, mul_comm (1 + _), mul_assoc, ← ih, mul_add, hshift]
      ring
  linarith

/-- Iterate the one-step construction on binary word spaces. The output is
reindexed by `Fin` so its size is available directly to the port construction. -/
theorem iterate_sparse_walk {m L d : ℕ} (hd : 0 < d) (hL : 0 < L) {α κ : ℝ}
    (ha : 1 < α) (hk : 0 ≤ κ)
    (step : ∀ (w k : ℕ) (P : Matrix (WordSpace w) (WordSpace w) ℝ) (γ : ℝ), 0 ≤ γ →
      SparseWalkBound X P k γ → ∃ Q : Matrix (Fin m → WordSpace w) (Fin m → WordSpace w) ℝ,
        SparseWalkBound X Q (L * (k + 2)) (α * γ + κ)) (j : ℕ) :
    ∃ P : Matrix (Fin ((2 ^ d) ^ (m ^ j))) (Fin ((2 ^ d) ^ (m ^ j))) ℝ,
      SparseWalkBound X P ((2 * L) ^ j * 2 ^ d) ((1 + κ / (α - 1)) * α ^ j) := by
  have hd₂ : 2 ≤ 2 ^ d := Nat.le_pow (by omega)
  have grow (i : ℕ) : 2 ≤ (2 * L) ^ i * 2 ^ d := hd₂.trans
    (Nat.le_mul_of_pos_left _ (pow_pos (by omega) i))
  have build (i : ℕ) : ∃ P : Matrix (WordSpace (d * m ^ i)) (WordSpace (d * m ^ i)) ℝ,
      SparseWalkBound X P ((2 * L) ^ i * 2 ^ d) (sparseCoefficient α κ i) := by
    induction i with
    | zero =>
      rw [pow_zero, Nat.mul_one, pow_zero, Nat.one_mul]
      simpa only [sparseCoefficient, card_wordSpace] using
        (show ∃ P : Matrix (WordSpace d) (WordSpace d) ℝ, SparseWalkBound X P (Fintype.card (WordSpace d)) 1
          from ⟨_, uniform_sparseWalkBound X (WordSpace d)⟩)
    | succ i ih =>
      obtain ⟨P, hP⟩ := ih
      obtain ⟨Q, hQ⟩ := step _ _ P _ (sparseCoefficient_nonneg (zero_le_one.trans ha.le) hk i) hP
      have hcard : Fintype.card (Fin m → WordSpace (d * m ^ i)) =
          Fintype.card (WordSpace (d * m ^ (i + 1))) := by
        simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul, pow_succ, Nat.mul_assoc]
      have hR := hQ.reindex (Fintype.equivOfCardEq hcard)
      refine ⟨_, {hR with support := fun u ↦ (hR.support u).trans ?_}⟩
      rw [pow_succ' (2 * L)]
      have hsum : (2 * L) ^ i * 2 ^ d + 2 ≤ 2 * ((2 * L) ^ i * 2 ^ d) := by
        linarith only [grow i]
      calc
        _ ≤ L * (2 * ((2 * L) ^ i * 2 ^ d)) := Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
  obtain ⟨P, hP⟩ := build j
  have hcard : Fintype.card (WordSpace (d * m ^ j)) = (2 ^ d) ^ (m ^ j) := by
    rw [card_wordSpace, pow_mul]
  have hR := hP.reindex (Fintype.equivFinOfCardEq hcard)
  refine ⟨_, {hR with bound := fun t x ↦ (hR.bound t x).trans ?_}⟩
  apply mul_le_mul_of_nonneg_right (sparseCoefficient_le ha hk j)
  exact Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦ mul_nonneg (hR.nonneg u v) (sq_nonneg _)

end SpectralGeometry

end VPVNP
end Computability
end OAI
