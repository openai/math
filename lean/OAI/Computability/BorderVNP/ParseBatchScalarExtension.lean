import OAI.Computability.BorderVNP.CrossingNetwork

/-! # Specialization of a network over the integer parameter ring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open Crossing

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Apply a coefficient map to each local table entry, preserving the physical wiring. -/
def mapTables (N : Network D P bits) (f : R →+* S) (t : N.Tables R) : N.Tables S :=
  fun v a x => f (t v a x)

/-- The equality of formal query polynomials from Lemma 2.3 specializes in every
characteristic. Scalar extensions and parameter substitutions commute with the
full finite contraction, including shared-index summation. -/
theorem value_mapTables (N : Network D P bits) (f : R →+* S) (t : N.Tables R) (x : Ports bits) :
    N.value (N.mapTables f t) x = f (N.value t x) := by
  classical
  simp only [Network.value, Network.read, mapTables, map_sum, map_prod]

end Crossing.Network

end BorderVNP
end Computability
end OAI
