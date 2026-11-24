import OAI.Computability.VPVNP.PermanentInterior
import OAI.Computability.VPVNP.PermanentExterior
import OAI.Computability.VPVNP.PermanentLabels
import OAI.Computability.VPVNP.ExactOneWeights

/-!
# Weighted exact-one assignments as a projection of the permanent

The squarefree interior coefficient enforces the equality gadget for each literal.
The exterior coefficient enforces consistent orientations of the variable rings. Finally,
there is exactly one compatible choice in each clause of a satisfying assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial HardnessCNF ExactOne
open scoped Classical

variable {k m c : ℕ} {R : Type*} [CommRing R]

private def compatibleChoices (occ : Fin m → Fin k × Fin c × Bool) (a : RingRow k m → Bool)
    (y : Fin c → Fin m) : Prop :=
  ownerOK occ y ∧ ∀ g, a (markedPosition occ g) = (occ g).2.2 ↔ y (occ g).2.1 = g

private theorem coeff_both_blocks (occ : Fin m → Fin k × Fin c × Bool) (w : Fin k → R)
    (b : R) (hb : -2 * b = 1) (a : RingRow k m → Bool) (y : Fin c → Fin m) :
    ((expandedTerm occ w b a y).coeff (fullDegree (Interior m))).coeff
        (fullDegree (Exterior k m c)) =
      if ∀ v j, a (v, j) = a (v, 0) then
        if compatibleChoices occ a y then ∏ u, ringWeight w u (a u) else 0
      else 0 := by
  rw [coeff_expandedTerm occ w b hb]
  split
  next h =>
    rw [coeff_C_mul, coeff_exterior_matched occ a y h.1 h.2]
    have h' : compatibleChoices occ a y := h
    rw [ite_eq_left h']
    split_ifs <;> simp
  next h =>
    have h' : ¬ compatibleChoices occ a y := h
    simp [h']

/-- The weighted graph computes exactly the generating polynomial of exact-one assignments. -/
theorem permanent_graph_eq_weighted (φ : CNF k) (w : Fin k → R) (b : R) (hb : -2 * b = 1) :
    (graphMatrix (occurrences φ) w b).permanent = weightedExactOne φ w := by
  let occ := occurrences φ
  let W (a : RingRow k (literalCount φ) → Bool) := ∑ y : Fin φ.length → Fin (literalCount φ),
    if compatibleChoices occ a y then ∏ u, ringWeight w u (a u) else 0
  rw [← coeff_rowProduct, coeff_fullDegree_sum, rowProduct_eq_expandedSum]
  simp only [coeff_sum, coeff_both_blocks _ w b hb]
  calc
    _ = ∑ a : RingRow k (literalCount φ) → Bool,
        if (∑ u, Finsupp.single (ringTarget u (a u)) 1) = fullDegree (RingRow k (literalCount φ))
        then W a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : ∀ v j, a (v, j) = a (v, 0) <;> simp [ringDegrees_eq_full_iff, h, W, occ]
    _ = ∑ x : Fin k → Bool, W (fun u => x u.1) := sum_ring_choices W
    _ = _ := by
      unfold weightedExactOne
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [W]
      rw [prod_ringWeight w (fun u : RingRow k (literalCount φ) => x u.1) x (fun _ _ => rfl)]
      convert! sum_clause_choices φ x (∏ i, if x i then w i else 1) using 2
      simp only [compatibleChoices, ownerOK, occ, markedPosition, iff_comm]
      split_ifs with h
      · exact ite_eq_left h
      · exact ite_eq_right h

/-- A p-projection with literal variable-or-constant entries, valid whenever the field's
characteristic is different from two. -/
theorem weighted_projection {F σ : Type*} [Field F] (q : ℕ) [CharP F q] (hq : q ≠ 2)
    (φ : CNF k) (w : Projection F (Fin k) σ) :
    let m := literalCount φ
    let n := 3 * m + k * (m + 2) + φ.length
    ∃ ρ : Projection F (Fin n × Fin n) σ, ρ.hom (permanentPolynomial F n) =
      weightedExactOne φ (fun i => (w i).elim X C) := by
  obtain ⟨ρ, hρ⟩ := weightedLabelsProjection (occurrences φ) w (-(2 : F)⁻¹)
  exact ⟨ρ, hρ.trans (permanent_graph_eq_weighted φ _ _ (map_neg_half_normalized q hq C))⟩

end PermanentReduction

end VPVNP
end Computability
end OAI
