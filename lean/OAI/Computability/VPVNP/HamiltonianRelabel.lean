import OAI.Computability.VPVNP.Hamiltonian
import OAI.Computability.VPVNP.Circuits

/-!
# Weighted directed Hamiltonian cycles on a finite vertex type

Relabel the vertices by matrix indices, substitute zero on forbidden arcs, and
put the indicated variable or scalar on each allowed arc. In the resulting
formal polynomial only the permitted spanning permutations contribute.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial
open scoped Classical

private theorem cycle_relabel {α β : Type*} (e : α ≃ β) {π : Equiv.Perm α}
    (h : π.IsCycleOn Set.univ) : (e.permCongr π).IsCycleOn Set.univ := by
  refine ⟨(e.permCongr π).bijective.bijOn_univ, fun x _ y _ => ?_⟩
  obtain ⟨i, hi⟩ := h.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y))
  refine ⟨i, ?_⟩
  change (e.permCongrHom π ^ i) x = y
  rw [← map_zpow]
  simp only [Equiv.permCongrHom_coe, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

/-- The projected matrix has the given arc label on allowed arcs and zero elsewhere. -/
theorem hamiltonian_projection_on_allowed {V R τ : Type*} [Fintype V] [CommRing R] {m : ℕ}
    (e : Fin m ≃ V) (hm : 0 < m) (ok : V → V → Prop) (w : V → V → τ ⊕ R) :
    ∃ ψ : Projection R (Fin m × Fin m) τ, ψ.hom (hamiltonianCyclePolynomial R m) =
      ∑ π : {π : Equiv.Perm V // π.IsCycleOn Set.univ ∧ ∀ i, ok i (π i)},
        ∏ i, (w i (π.val i)).elim X C := by
  classical
  let ψ : Projection R (Fin m × Fin m) τ := fun (i,j) =>
    if ok (e i) (e j) then w (e i) (e j) else .inr 0
  let good (π : Equiv.Perm V) := π.IsCycleOn Set.univ ∧ ∀ i, ok i (π i)
  let weight (π : Equiv.Perm V) := ∏ i, (w i (π i)).elim (X (R := R)) C
  refine ⟨ψ, ?_⟩
  change ψ.hom (hamiltonianCyclePolynomial R m) = ∑ π : {π // good π}, weight π.val
  rw [← Finset.sum_subtype (Finset.univ.filter good) (by simp) weight, Finset.sum_filter,
    ← e.permCongr.sum_comp (fun π => if good π then weight π else 0)]
  simp only [hamiltonianCyclePolynomial, spanningCycles, map_sum, Finset.sum_filter,
    hm, true_and]
  apply Finset.sum_congr rfl
  intro π _
  have hc : (e.permCongr π).IsCycleOn Set.univ ↔ π.IsCycleOn Set.univ := by
    constructor
    · intro hc
      have hr := cycle_relabel e.symm hc
      change (e.permCongr.symm (e.permCongr π)).IsCycleOn Set.univ at hr
      rw [Equiv.symm_apply_apply] at hr
      exact hr
    · exact cycle_relabel e
  by_cases hcycle : π.IsCycleOn Set.univ
  · simp only [hcycle, ite_true, good, hc, true_and, map_prod]
    by_cases hok : ∀ i, ok i (e.permCongr π i)
    · rw [ite_eq_left hok]
      dsimp only [weight]
      rw [← e.prod_comp (fun i => (w i (e.permCongr π i)).elim X C)]
      apply Finset.prod_congr rfl
      intro i _
      have hi : ok (e i) (e (π i)) := by simpa using hok (e i)
      simp [Projection.hom, ψ, hi]
    · rw [ite_eq_right hok]
      obtain ⟨v, hv⟩ := not_forall.mp hok
      apply Finset.prod_eq_zero (Finset.mem_univ (e.symm v))
      have hi : ¬ok v (e (π (e.symm v))) := hv
      simp [Projection.hom, ψ, hi]
  · simp [hcycle, good, hc]

end VPVNP
end Computability
end OAI
