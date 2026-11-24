import OAI.Computability.VPVNP.HCForwardSpanning
import OAI.Computability.VPVNP.HCReadback
import OAI.Computability.VPVNP.HamiltonianRelabel
import OAI.Computability.VPVNP.ExactOneOccurrences
import OAI.Computability.VPVNP.ExactOneWeights

/-!
# Exact-one generating polynomials as Hamiltonian-cycle projections

Each satisfying assignment yields one allowed spanning cycle. Its entry arcs
record the selected variable weights. Summing the weights of these cycles
therefore gives the weighted exact-one polynomial over any commutative ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

open MvPolynomial Equiv
open scoped Classical

variable {R τ : Type*} [CommSemiring R] {k h c : ℕ}
variable (occ : Fin h → Fin k × Fin c × Bool)

/-- The entering arc records a true bit by its variable or scalar weight. All
other allowed arcs carry one. -/
def arcWeight (w : Projection R (Fin k) τ) : Vertex k h c → Vertex k h c → τ ⊕ R
  | .sep i, .endpoint _ false => w i
  | _, _ => .inr 1

theorem product_cycleOfAssignment (w : Projection R (Fin k) τ) (x : Fin k → Bool)
    (hx : Exact occ x) :
    (∏ v, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C) =
      ∏ i, if x i then (w i).elim X C else 1 := by
  classical
  let S : Finset (Vertex k h c) := Finset.univ.image Vertex.sep
  have toS : (∏ v, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C) =
      ∏ v ∈ S, (arcWeight w v (cycleOfAssignment occ x hx v)).elim X C := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    cases v with
    | sep i => exact False.elim (hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    | endpoint | buffer | port | clause => simp [arcWeight]
  rw [toS, show S = _ from rfl, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    cases hi : x i <;> simp [nextVertex, hi, arcWeight]
  · exact fun _ _ _ _ he => Vertex.sep.inj he

/-- Spanning cycles in the exact-one gadget that follow an allowed directed edge at every
vertex. -/
abbrev Admissible (occ : Fin h → Fin k × Fin c × Bool) :=
  {π : Perm (Vertex k h c) // π.IsCycleOn Set.univ ∧ ∀ v, Allowed occ v (π v)}

/-- Turn an exact satisfying assignment into its directed spanning cycle through the variable
tracks and clause vertices. -/
noncomputable def toCycle (hk : 0 < k) (x : {x : Fin k → Bool // Exact occ x}) : Admissible occ :=
  ⟨cycleOfAssignment occ x x.2, cycleOfAssignment_spanning occ x x.2 hk, nextVertex_allowed occ x x.2⟩

/-- The weight-preserving encoding of exact-one assignments as allowed Hamiltonian tours. -/
noncomputable def assignmentsEquiv (hk : 0 < k) :
    {x : Fin k → Bool // Exact occ x} ≃ Admissible occ :=
  Equiv.ofBijective (toCycle occ hk) ⟨
    fun _ _ e => cycleOfAssignment_injective occ (congrArg Subtype.val e),
    fun π => by
      obtain ⟨x, hx, he⟩ := exists_exact_assignment π.2.1 π.2.2
      exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩⟩

section

variable {S : Type*} [CommRing S]

theorem weightedProjectionSlots (hk : 0 < k) (w : Projection S (Fin k) τ) :
    ∃ ψ : Projection S (Fin (k * (3 * h + 4) + c) × Fin (k * (3 * h + 4) + c)) τ,
      ψ.hom (hamiltonianCyclePolynomial S (k * (3 * h + 4) + c)) =
        ∑ x : {x : Fin k → Bool // Exact occ x}, ∏ i, if x.val i then (w i).elim X C else 1 := by
  classical
  let e := (Fintype.equivFinOfCardEq (card_vertex k h c)).symm
  have hm : 0 < k * (3 * h + 4) + c := Nat.add_pos_left (Nat.mul_pos hk (by omega)) _
  obtain ⟨ψ, he⟩ := hamiltonian_projection_on_allowed e hm (Allowed occ) (arcWeight w)
  refine ⟨ψ, he.trans ?_⟩
  symm
  let aweight (x : {x : Fin k → Bool // Exact occ x}) :=
    ∏ i, if x.val i then (w i).elim X C else 1
  let cweight (π : Admissible occ) := ∏ v, (arcWeight w v (π.val v)).elim X C
  refine @Fintype.sum_equiv _ _ _ ?_ ?_ _ (assignmentsEquiv occ hk) aweight cweight ?_
  intro x
  exact (product_cycleOfAssignment occ w x.val x.2).symm

/-- Projection from a Hamiltonian polynomial of explicit order for any positive-width
exact-one formula, allowing repeated literals and empty clauses. -/
theorem weighted_projection (φ : HardnessCNF.CNF k) (hk : 0 < k) (w : Projection S (Fin k) τ) :
    ∃ ψ : Projection S (Fin (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length) ×
        Fin (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length)) τ,
      ψ.hom (hamiltonianCyclePolynomial S (k * (3 * HardnessCNF.literalCount φ + 4) + φ.length)) =
        ExactOne.weightedExactOne φ (fun i => (w i).elim X C) := by
  obtain ⟨ψ, he⟩ := weightedProjectionSlots (ExactOne.occurrences φ) hk w
  refine ⟨ψ, he.trans ?_⟩
  rw [ExactOne.weightedExactOne_eq_sum]
  let e : {x : Fin k → Bool // Exact (ExactOne.occurrences φ) x} ≃
      {x : Fin k → Bool // ExactOne.Holds φ x} := Equiv.subtypeEquivRight (fun x => (ExactOne.holds_iff_unique_occurrence φ x).symm)
  let wt (x : Fin k → Bool) : MvPolynomial τ S := ∏ i, if x i then (w i).elim X C else 1
  exact Fintype.sum_equiv e (fun x => wt x.val) (fun x => wt x.val) fun _ => rfl

end

end HCGadget

end VPVNP
end Computability
end OAI
