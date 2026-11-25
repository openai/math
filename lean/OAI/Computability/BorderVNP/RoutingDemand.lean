import OAI.Computability.BorderVNP.RoutingCapacity

/-!
# Incidence of shared lists and literal deliveries

In §8.3, lists assigned to a single team are read locally and do not need a
physical transmission. Every other list or delivery is routed once. The team
weight of §8.2 pays for both incident ends of shared lists and all incoming
deliveries. Proposition 7.2 pays for outgoing literal data separately.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Filter TeamScales

variable {R : ℕ} {Item : Type*} [Fintype Item]

/-- Total width of descriptors with the given ordered source and destination. -/
def orderedWidth (src dst : Item → Fin R) (bits : Item → ℕ) (u v : Fin R) : ℕ :=
  ∑ i, if src i = u ∧ dst i = v then bits i else 0

/-- The unordered list at each pair concatenates both orientations. -/
def combinedWidth (src dst : Item → Fin R) (bits : Item → ℕ) (u v : Fin R) : ℕ :=
  orderedWidth src dst bits u v + orderedWidth src dst bits v u

/-- Bits paid for at one specified endpoint, restricting to a class of descriptors. -/
def teamBits (endpoint : Item → Fin R) (bits : Item → ℕ) (kind : Item → Bool) (u : Fin R) : ℕ :=
  ∑ i, if kind i ∧ endpoint i = u then bits i else 0

private theorem oneEnd (src dst : Item → Fin R) (bits : Item → ℕ) (u : Fin R) :
    ∑ v, orderedWidth src dst bits u v = ∑ i, if src i = u then bits i else 0 := by
  simp only [orderedWidth]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : src i = u <;> simp [h, eq_comm]

private theorem splitTeamBits (ep : Item → Fin R) (bits : Item → ℕ) (data : Item → Bool)
    (u : Fin R) : (∑ i, if ep i = u then bits i else 0) =
      teamBits ep bits (!data ·) u + teamBits ep bits data u := by
  rw [teamBits, teamBits, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases data i <;> simp

/-- Raw incidence overestimates the actual traffic, since co-located data
and co-located shared lists disappear from the physical blocks. -/
theorem incidence_le (src dst : Item → Fin R) (bits : Item → ℕ) (data : Item → Bool)
    (u : Fin R) :
    ∑ v, demand (combinedWidth src dst bits) u v ≤
      teamBits src bits (!data ·) u + teamBits dst bits (!data ·) u +
        teamBits dst bits data u + teamBits src bits data u := by
  have reverse (v : Fin R) : orderedWidth src dst bits v u = orderedWidth dst src bits u v := by
    simp [orderedWidth, and_comm]
  calc
    _ ≤ ∑ v, (orderedWidth src dst bits u v + orderedWidth dst src bits u v) := by
      apply Finset.sum_le_sum
      intro v _
      rw [← reverse v]
      by_cases hu : u = v
      · simp [demand, hu]
      · rcases le_total u v with huv | hvu
        · simp [demand, hu, min_eq_left huv, max_eq_right huv, combinedWidth]
        · simp [demand, hu, min_eq_right hvu, max_eq_left hvu, combinedWidth, add_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, oneEnd, oneEnd, splitTeamBits src bits data, splitTeamBits dst bits data]
      omega

/-- Adding the two or three allowed literal fields preserves the incidence
budget required by (8.2), uniformly over all team sizes and descriptor lists. -/
theorem eventually_incidence {ξ α : ℝ} (hlit : ξ < α / 3) :
    ∀ᶠ n : ℕ in atTop, ∀ (r : ℕ) (src dst : Item → Fin R) (bits : Item → ℕ)
      (data : Item → Bool) (u : Fin R),
      256 * (teamBits src bits (!data ·) u + teamBits dst bits (!data ·) u +
        teamBits dst bits data u) ≤ exterior ξ r n →
      teamBits src bits data u ≤ 3 * r * literal α n →
      ∑ v, demand (combinedWidth src dst bits) u v ≤ exterior ξ r n / 64 := by
  filter_upwards [eventually_literals_le hlit 768] with n hn
  intro r src dst bits data u assigned outgoing
  have ho : 256 * teamBits src bits data u ≤ exterior ξ r n := calc
    _ ≤ 256 * (3*r*literal α n) := Nat.mul_le_mul_left _ outgoing
    _ = 768*r*literal α n := by ring
    _ ≤ _ := hn r
  have hi := incidence_le src dst bits data u
  omega

end Routing

end BorderVNP
end Computability
end OAI
