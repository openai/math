import OAI.Combinatorics.KMedian.Expanders.ExpanderFamily

/-! # A scalar expander on a padded dyadic vertex set -/

namespace OAI.Computability.MultitapeWeakETH

open MetricKMedian.PCP Finset
open scoped BigOperators

/-- A half-contraction on mean-zero real functions yields a scalar Poincaré
constant of two, for ordered independent pairs and uniform directed ports. -/
theorem scalar_poincare {V D : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (contract : G.Contracts (1/2)) (f : V → ℝ) :
    (𝔼 v, 𝔼 w, (f v-f w)^2) ≤ 2 * (𝔼 v, 𝔼 d, (f v - f (G.step v d))^2) := by
  let g (v : V) := f v - 𝔼 w, f w
  have zero : (𝔼 v, g v) = 0 := by simp [g,expect_sub_distrib]
  have point (v w : V) : (f v-f w)^2 = g v^2 + g w^2 - 2 * (g v * g w) := by
    dsimp [g]; ring
  have pairs : (𝔼 v, 𝔼 w, (f v-f w)^2) = 2 * energy g := by
    simp_rw [point,expect_sub_distrib,expect_add_distrib,← mul_expect]
    simp [zero,energy,two_mul]
  have arcs : (𝔼 v, 𝔼 d, (f v - f (G.step v d))^2) =
      2 * energy g - 2 * pairing g (G.adjacency g) := by
    simp_rw [point,expect_sub_distrib,expect_add_distrib,← mul_expect]
    simp only [Fintype.expect_const]
    change ((𝔼 v, g v^2) + (𝔼 v, G.adjacency (fun w => g w^2) v)) - _ = _
    rw [G.adjacency_mean]
    simp only [energy,two_mul,pairing,PortGraph.adjacency]
  have CS := pairing_le_l2 g (G.adjacency g)
  have half := G.l2_contracts (by norm_num : (0:ℝ) ≤ 1/2) contract g zero
  rw [pairs,arcs]
  nlinarith only [CS,mul_le_mul_of_nonneg_left half (l2_nonneg g),l2_sq g]

/-- The existing zigzag family can pad an arbitrary positive order to a
power of two at most a fixed constant times that order. Degree is fixed. -/
theorem padded_scalar_expander (n : ℕ) :
    let k := ExpanderFamily.level n
    let V := ExpanderFamily.Vertex k
    n+1 ≤ Fintype.card V ∧ Fintype.card V ≤ 2^176*(n+1) ∧
      Fintype.card V = 2^(176*k) ∧ Fintype.card ExpanderFamily.Degree = 2^88 ∧
      ∀ f : V → ℝ, (𝔼 v, 𝔼 w, (f v-f w)^2) ≤
        2 * (𝔼 v, 𝔼 d, (f v - f ((ExpanderFamily.graph k).step v d))^2) := by
  dsimp only
  have growth : ExpanderFamily.growth = 2^176 := by
    unfold ExpanderFamily.growth
    rw [← pow_mul]
  refine ⟨ExpanderFamily.padding_lower n,by simpa only [← growth] using ExpanderFamily.padding_upper n,
    by rw [ExpanderFamily.card_vertex,growth,pow_mul],?_,?_⟩
  · change Fintype.card (Fin (2^44) × Fin (2^44)) = 2^88
    rw [Fintype.card_prod,Fintype.card_fin,← pow_add]
  · exact scalar_poincare _ (ExpanderFamily.graph_contracts _)

end OAI.Computability.MultitapeWeakETH
