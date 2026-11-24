import OAI.Computability.VPVNP.GrassmannSampling
import OAI.Computability.VPVNP.SparseParameters
import OAI.Computability.VPVNP.SparseWalkIteration

/-!
# The rounded sparse Grassmann family

Section 5.2 of *VP and VNP differ over every field* constructs a common graph
for an entire class of targets from their strict Grassmann inequality. Its
order is `D ^ (m ^ j)`, its power-of-two degree is at most `4 Cj D`, and its
Poincaré coefficient grows as `O(α ^ j)` for `α < m`. The degree constant may
depend on `j`, while the coefficient prefactor is independent of both `D` and `j`.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open SpectralGeometry

variable {n : ℕ}

/-- The same linear map is sampled for every plane. On complementary pairs its
two readings are independent, and on adjacent pairs their extensions are
conditionally independent given the restriction to the intersection. -/
theorem exists_readPlane_laws (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] [Fintype E] :
    ∃ l r : Pair (n+1) 1 → ((Fin n → E) × E) ≃ (Fin (n+1) → E),
      PairSamplingLaws (fun f U ↦ readPlane E U f) l r := by
  choose l r hr using exists_adjacent_charts (n := n) E
  exact ⟨l, r, ⟨fun p g ↦ average_read_complement E p.property g, hr⟩⟩

variable {T : Type*} (X : T → Type*) [∀ t, PseudoMetricSpace (X t)]

private theorem sparseStep [Nonempty (Pair (n+1) (n+1))] [Nonempty (Pair (n+1) 1)]
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c)
    (hgrass : ∀ t (f : Plane (n+1) → X t), mean (fun a b ↦ dist (f a) (f b) ^ 2) (n+1) ≤
      c * mean (fun a b ↦ dist (f a) (f b) ^ 2) 1)
    (w k : ℕ) (P : Matrix (WordSpace w) (WordSpace w) ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hP : SparseWalkBound X P k γ) :
    ∃ Q : Matrix (Fin (n+1) → WordSpace w) (Fin (n+1) → WordSpace w) ℝ,
      SparseWalkBound X Q (Fintype.card (Pair (n+1) 1) * (k + 2))
        ((c * (1 + ε)) * γ + c * (1 + 1 / ε)) := by
  obtain ⟨l,r,h⟩ := exists_readPlane_laws (n := n) (WordSpace w)
  let a := (1 + ε) * γ
  let b := 1 + 1 / ε
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨sparseWalk l r P a b, ⟨sparseWalk_nonneg _ _ _ hP.nonneg ha hb.le,
    sparseWalk_row _ _ _ hP.row (add_pos_of_nonneg_of_pos ha hb).ne',
    sparseWalk_symm _ _ _ hP.symm _ _, sparseWalk_support _ _ _ _ _ hP.support, ?_⟩⟩
  intro t
  have ht := h.sparseBound P hε hγ hc (hP.bound t) (hgrass t)
  simpa only [mul_add, ← mul_assoc, a, b] using ht

/-- Sparse regular multigraphs of order `D^(m^j)` for every starting order
`D=2^d≥2`. The choices of the matrices and of their power-of-two degrees are
simultaneous for all the targets satisfying the strict Grassmann inequality. -/
theorem exists_sparse_rounded_family {m : ℕ} (hm : 1 < m) {c₀ : ℝ} (hc₀ : c₀ < m)
    (hgrass : ∀ t (f : Plane m → X t), mean (fun a b ↦ dist (f a) (f b) ^ 2) m ≤
      c₀ * mean (fun a b ↦ dist (f a) (f b) ^ 2) 1) :
    ∃ α C' : ℝ, 1 < α ∧ α < m ∧ 0 ≤ C' ∧ ∀ j : ℕ, ∃ Cj : ℕ, 0 < Cj ∧ ∀ d : ℕ, 0 < d →
      ∃ e : ℕ, 2 ^ e ≤ 4 * Cj * 2 ^ d ∧
        ∃ M : Matrix (Fin ((2 ^ d) ^ (m ^ j))) (Fin ((2 ^ d) ^ (m ^ j))) ℕ,
          (∀ i j, M i j = M j i) ∧ (∀ i, ∑ j, M i j = 2 ^ e) ∧
            ∀ t, HasPoincareBound (X t) (normalizeArcs M (2 ^ e)) (2 * C' * α ^ j) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  let := nonempty_pair (Nat.le_refl (n+1))
  let := nonempty_pair (show 1 ≤ n+1 by omega)
  obtain ⟨c,ε,hc₀c,hc,hε,ha,ham⟩ := exists_sparse_parameters (by exact_mod_cast hm) hc₀
  let α := c * (1 + ε)
  let κ := c * (1 + 1 / ε)
  let C' := 1 + κ / (α - 1)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hα : 1 < α := ha
  have hC : 0 ≤ C' := by dsimp only [C']; positivity
  have hbig (t : T) (f : Plane (n+1) → X t) : mean (fun a b ↦ dist (f a) (f b) ^ 2) (n+1) ≤
      c * mean (fun a b ↦ dist (f a) (f b) ^ 2) 1 := by
    refine (hgrass t f).trans (mul_le_mul_of_nonneg_right hc₀c ?_)
    exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)
  let L := Fintype.card (Pair (n+1) 1)
  have hL : 0 < L := Fintype.card_pos
  refine ⟨α, C', hα, ham, hC, fun j ↦ ⟨(2 * L) ^ j, by positivity, fun d hd ↦ ?_⟩⟩
  obtain ⟨P,hP⟩ := iterate_sparse_walk hd hL ha hκ (sparseStep X hε hc hbig) j
  obtain ⟨e,_,he,M,hM,hrow,hhalf⟩ := exists_regular_rounding P (by positivity) hP.nonneg
    hP.row hP.symm hP.support
  refine ⟨e, by simpa only [Nat.mul_assoc] using he, M, hM, hrow, fun t ↦ ?_⟩
  rw [mul_assoc]
  exact hasPoincareBound_of_half_le hhalf (mul_nonneg hC (pow_nonneg (zero_le_one.trans hα.le) _)) (hP.bound t)

end Grassmann

end VPVNP
end Computability
end OAI
