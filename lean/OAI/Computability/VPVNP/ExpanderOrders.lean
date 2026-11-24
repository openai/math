import OAI.Computability.VPVNP.CloudIteration

/-!
# Arbitrarily large dyadic graph orders

Section 5.3 of *VP and VNP differ over every field* iterates a fixed port graph
and then removes loops by doubling. A real line in the target class forces
each resulting multigraph to be connected.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {T : Type*} (Y : T → Type*) [∀ a, PseudoMetricSpace (Y a)]
  [∀ a, CompleteSpace (Y a)] [∀ a, Nonempty (Y a)]

/-- A port graph of dyadic order and degree yields connected, loopless
multigraphs of unbounded dyadic order, with one degree and one Poincaré
bound for all orders and targets. -/
theorem exists_expander_orders {s e n : ℕ} (hs : 0 < s) (hn : 0 < n)
    (H : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℕ) (hHs : ∀ i j, H i j = H j i)
    (hHr : ∀ i, ∑ j, H i j = 2 ^ e) {β : ℝ} (hβ : 1 ≤ β)
    (ht : 1776 * β ≤ 2 * (n : ℝ))
    (hdiv : (2 * n) * (2 * (2 * 2 ^ e)) ^ (2 * n) ∣ 2 ^ s)
    (hcat : ∀ a, HasCATZeroSegments (Y a))
    (hH : ∀ a, HasPoincareBound (Y a) (normalizeArcs H (2 ^ e)) β)
    (realTarget : T) (embed : ℝ → Y realTarget)
    (h_embed : ∀ a b, dist (embed a) (embed b) = dist a b) (minimum : ℕ) :
    ∃ o : ℕ, minimum ≤ 2 ^ o ∧
      ∃ G : Matrix (Fin (2 ^ o)) (Fin (2 ^ o)) ℕ, (∀ i j, G i j = G j i) ∧
        (∀ i, G i i = 0) ∧ (∀ i, ∑ j, G i j = 2 ^ (e + 2)) ∧
        (∀ i j, Relation.ReflTransGen (fun a b ↦ 0 < G a b) i j) ∧
        ∀ a, HasPoincareBound (Y a) (normalizeArcs G (2 ^ (e + 2))) (6 + 12 * (444 * β)) := by
  have order : 2 * (2 ^ s) ^ minimum = 2 ^ (s * minimum + 1) := by
    rw [pow_succ, pow_mul, Nat.mul_comm]
  have degree : 4 * 2 ^ e = 2 ^ (e + 2) := by
    rw [pow_add, Nat.mul_comm, show (2 : ℕ) ^ 2 = 4 by decide]
  have hmin : minimum ≤ 2 ^ (s * minimum + 1) := by
    apply minimum.lt_two_pow_self.le.trans
    apply Nat.pow_le_pow_right (by decide)
    have := Nat.mul_le_mul_right minimum (show 1 ≤ s from hs)
    omega
  have doubled := exists_looplessCloudGraph Y (by positivity) (by positivity) hn
    H hHs hHr hβ ht hdiv hcat hH minimum
  rw [order, degree] at doubled
  obtain ⟨G, hsymm, hregular, hloop, hbound⟩ := doubled
  refine ⟨s * minimum + 1, hmin, G, hsymm, hloop, hregular, ?_, hbound⟩
  let P := normalizeArcs G (2 ^ (e + 2))
  have hsep : 0 < dist (embed 0) (embed 1) := by rw [h_embed]; norm_num [Real.dist_eq]
  have nonnegP (i j) : 0 ≤ P i j := by unfold P normalizeArcs; positivity
  have symmP (i j) : P i j = P j i := by simp only [P, normalizeArcs, hsymm i j]
  intro i j
  apply Relation.ReflTransGen.mono _ i j <|
    reachable_of_poincare (embed 0) (embed 1) hsep P nonnegP symmP (hbound realTarget) i j
  intro a b hab
  have hpos : (0 : ℝ) < G a b := (div_pos_iff_of_pos_right (by positivity)).mp hab
  exact_mod_cast hpos

end SpectralGeometry

end VPVNP
end Computability
end OAI
