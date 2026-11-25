import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.RootedHamiltonian
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.TourMarkerCancellation

/-! # The option-and-marker graph projects onto Hamiltonian cycle

This is the initial graph of the binary-witness construction. Its two
weights distinguish absence and presence. The signed marker cancellation
takes place integrally, before any field specialization.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace IndependentSetGraph

open scoped Classical BigOperators
noncomputable section

abbrev TourVertex (m : ℕ) := TourOption m ⊕ Fin m
abbrev TourEdge (m : ℕ) := TourOption.Edge m ⊕ TourOption m

def tourLeft (m : ℕ) : TourEdge m → TourVertex m := markedLeft TourOption.left

def tourRight (m : ℕ) : TourEdge m → TourVertex m := markedRight TourOption.right TourOption.pos

theorem tour_no_loops (m : ℕ) (e : TourEdge m) : tourLeft m e ≠ tourRight m e := by
  cases e with
  | inl e => exact fun h => e.property.2.1 (Sum.inl.inj h)
  | inr a => exact Sum.inl_ne_inr

/-- Occupied options keep their edge variable. All other substitutions are
constants, with a minus sign on an occupied marker. -/
def tourProjection (R : Type*) [CommRing R] (m : ℕ) :
    TourVertex m × Bool → ProjectionAtom R (Fin m × Fin m) :=
  markedProjection (fun a => .inl (a.src, a.dst))

/-- The option-and-marker homogeneous independent-set polynomial
projects to the directed Hamiltonian-cycle polynomial. -/
theorem tour_projection (R : Type*) [CommRing R] {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    project (tourProjection R m) (polynomial R (tourLeft m) (tourRight m)) =
      hamiltonianCyclePolynomial R m := by
  rw [tourProjection, tourLeft, tourRight, project_markedPolynomial]
  refine Eq.trans ?_ ((sum_coveringOptions hm (fun a b => MvPolynomial.X (R := R) (a,b))).trans
    (rootedTour_sum_eq_cycles hm (fun a b => MvPolynomial.X (R := R) (a,b))))
  congr 1
  · ext x
    simp
  · funext x
    by_cases h : independent TourOption.left TourOption.right x ∧ coveringOptions x <;>
      simp_all [coveringOptions, atomPolynomial]


theorem tour_option_card_le (m : ℕ) : Fintype.card (TourOption m) ≤ m^3 := by
  have h := Fintype.card_le_of_injective (Subtype.val : TourOption m → _) Subtype.val_injective
  simpa [Fintype.card_prod, pow_succ, Nat.mul_assoc] using h

theorem tour_vertex_card_ge (m : ℕ) : m ≤ Fintype.card (TourVertex m) := by
  simp [TourVertex]

theorem tour_vertex_card_le (m : ℕ) : Fintype.card (TourVertex m) ≤ m^3 + m := by
  rw [Fintype.card_sum, Fintype.card_fin]
  exact Nat.add_le_add_right (tour_option_card_le m) _

theorem tour_edge_card_le (m : ℕ) : Fintype.card (TourEdge m) ≤ m^6 + m^3 := by
  have he := Fintype.card_le_of_injective (Subtype.val : TourOption.Edge m → _) Subtype.val_injective
  rw [Fintype.card_prod] at he
  rw [Fintype.card_sum]
  have h := tour_option_card_le m
  apply Nat.add_le_add _ h
  exact he.trans ((Nat.mul_le_mul h h).trans_eq (by ring))

end
end IndependentSetGraph

end SpectralBooks
end LinearAlgebra
end OAI
