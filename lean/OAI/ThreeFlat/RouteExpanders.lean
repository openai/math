import OAI.ThreeFlat.TabulatedRouting
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI
/-! # Routing expanders of every power-of-two order

The square-zigzag step increases the base-two logarithm of the order by 448
and preserves both the port type and the half spectral bound. A Cayley seed
for each of the 448 possible remainders permits every required order.
Repeated squaring then gives a uniformly bounded degree for each tolerance.
-/

namespace ThreeFlat.RouteUnits

open BinPackingGames.Foundations.PCP PoweringWalks SpectralReturn

/-- Squaring amplifies the spectral bound while keeping the degree independent
of the vertex count, including when that count is a small power of two. -/
theorem exists_powered_routing_graphs (j : ℕ) :
    ∃ h : ℕ, 2 ^ j ≤ h ∧ ∀ k : ℕ,
      ∃ G : PortGraph (Fin (2 ^ k)) (Fin (2 * h)),
        SpectralCertificate G ((1 / 2 : ℝ) ^ (2 ^ j)) :=
  powered_routing_graphs_of_tables j

/-- The bipartite double cover of the returned port graph can be used between
the source and receiver copies of the bundle positions. The same even degree
works for every bundle count that is a power of two. -/
theorem exists_routing_graphs (minHalfDegree : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℕ, 0 < h ∧ minHalfDegree ≤ h ∧ ∃ lam : ℝ, lam ^ 2 ≤ ε ∧ ∀ k : ℕ,
      ∃ G : PortGraph (Fin (2 ^ k)) (Fin (2 * h)),
        SpectralCertificate G lam := by
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let j := t + minHalfDegree
  have large := j.lt_two_pow_self
  obtain ⟨h, hh, graphs⟩ := exists_powered_routing_graphs j
  refine ⟨h, by omega, by dsimp [j] at large hh; omega, (1 / 2 : ℝ) ^ (2 ^ j), ?_, graphs⟩
  rw [← pow_mul]
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (by dsimp [j] at *; omega : t ≤ 2 ^ j * 2)).trans ht.le

end ThreeFlat.RouteUnits

end OAI
