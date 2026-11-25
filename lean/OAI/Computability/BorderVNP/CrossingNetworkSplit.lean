import OAI.Computability.BorderVNP.CrossingThreeJunction
import OAI.Computability.BorderVNP.CrossingBalancedLayouts
import OAI.Computability.BorderVNP.CrossingSplit
import OAI.Computability.BorderVNP.CrossingClosure

/-!
# Closure of the three-junction layouts

The parameters of each first-side split vary independently in (4.3). Contracting
against the fixed opposite sides and summing is polynomial in all those parameters.
Each actual split gives genuine local tables on the same fixed layouts, so this
polynomial map puts the full tensor in the closure of sums of these networks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open MvPolynomial VPVNP
open scoped BigOperators

/-- The two-side contraction at the external ports. The same bridge label is read on
both sides, while opposite terminals enter the two side tables. -/
noncomputable def sidesContraction {D p m : ℕ} {K : Type*} [CommSemiring K]
    (A opposite : (Fin D → Bool) → ((Fin D ⊕ Fin p) → Fin (2 ^ m)) → K)
    (x : Ports (fun _ : Fin D × Bool => m)) : K :=
  ∑ o, ∑ j, opposite o (junctionLabels m (fun i => !o i) x j) * A o (junctionLabels m o x j)

variable {D p m r : ℕ} {K : Type*} [Field K]

/-- Replacing each approximated side by an actual balanced split gives tables on
these same finite network layouts. Only the tensor entries vary inside the closure. -/
theorem split_contraction_mem_closure
    (A opposite : (Fin D → Bool) → ((Fin D ⊕ Fin p) → Fin (2 ^ m)) → K)
    (hA : ∀ o, A o ∈ imageClosure (balancedCutSums (Fin D ⊕ Fin p) (Fin (2 ^ m)) K r))
    (g : BalancedPlacements D p) :
    sidesContraction A opposite ∈ imageClosure
      (Set.range fun tab : ∀ t, (g.net m r t).Tables K => fun x => ∑ t, (g.net m r t).value (tab t) x) := by
  classical
  let S := balancedCutSums (Fin D ⊕ Fin p) (Fin (2 ^ m)) K r
  have hRange : Set.range (fun u : S => u.val) = S := Set.Subset.antisymm
    (fun _ ⟨u, hu⟩ => hu ▸ u.property) (fun u hu => ⟨⟨u, hu⟩, rfl⟩)
  let Q (x : Ports (fun _ : Fin D × Bool => m)) :
      MvPolynomial ((_ : Fin D → Bool) × ((Fin D ⊕ Fin p) → Fin (2 ^ m))) K :=
    ∑ o, ∑ j, C (opposite o (junctionLabels m (fun i => !o i) x j)) * X ⟨o, junctionLabels m o x j⟩
  have h := imageClosure_joint_contraction (fun (_ : Fin D → Bool) (u : S) => u.val) A
    (fun o => hRange.symm ▸ hA o) Q
  simp only [Q, map_sum, map_mul, eval_C, eval_X, Sigma.uncurry] at h
  apply imageClosure_mono _ h
  rintro y ⟨u, rfl⟩
  have hu (o : Fin D → Bool) := (u o).property
  choose F hF using hu
  refine ⟨fun t : LayoutIndex D p => junctionTables t.1 t.2.val (g.moved t) (g.point t) (g.in_ball t)
    (F t.1 t.2.val) (opposite t.1), ?_⟩
  funext x
  simp only [BalancedPlacements.net, Fintype.sum_prod_type, junctionNetwork_value]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, hF o (junctionLabels m o x j)]
  congr 1
  simp only [Fintype.card_sum, Fintype.card_fin]
  exact (Finset.sum_coe_sort (balancedCuts D p) (fun I => (F o I).matrix
    (fun i => junctionLabels m o x j i.val) (fun i => junctionLabels m o x j i.val)))

end Crossing

end BorderVNP
end Computability
end OAI
