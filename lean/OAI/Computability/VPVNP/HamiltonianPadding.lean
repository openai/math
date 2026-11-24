import OAI.Computability.VPVNP.Circuits
import OAI.Computability.VPVNP.Hamiltonian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Perm.Fin

/-!
# Subdividing a forced arc of a directed Hamiltonian cycle

Section 15.1 of *VP and VNP differ over every field* pads the directed
Hamiltonian-cycle polynomial by one vertex. Number the new vertex by zero
and embed the old vertices by `Fin.succ`.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Equiv Equiv.Perm MvPolynomial

/-- Insert vertex zero immediately after the old vertex `a` in its cycle. -/
def subdivideCycle {m : ℕ} (a : Fin m) (π : Perm (Fin m)) : Perm (Fin (m + 1)) :=
  decomposeFin.symm ((π a).succ, π)

@[simp] theorem subdivideCycle_zero {m : ℕ} (a : Fin m) (π : Perm (Fin m)) :
    subdivideCycle a π 0 = (π a).succ := by simp [subdivideCycle]

@[simp] theorem subdivideCycle_at {m : ℕ} (a : Fin m) (π : Perm (Fin m)) :
    subdivideCycle a π a.succ = 0 := by simp [subdivideCycle]

@[simp] theorem subdivideCycle_away {m : ℕ} (a : Fin m) (π : Perm (Fin m))
    {i : Fin m} (hi : i ≠ a) : subdivideCycle a π i.succ = (π i).succ := by
  simp [subdivideCycle, swap_apply_of_ne_of_ne, hi]

theorem subdivideCycle_injective {m : ℕ} (a : Fin m) : Function.Injective (subdivideCycle a) := by
  intro π τ h
  exact congrArg Prod.snd (decomposeFin.symm.injective h)

theorem range_subdivideCycle {m : ℕ} (a : Fin m) (σ : Perm (Fin (m + 1))) :
    (∃ π, subdivideCycle a π = σ) ↔ σ a.succ = 0 := by
  constructor
  · rintro ⟨π, rfl⟩
    exact subdivideCycle_at _ _
  · obtain ⟨⟨p, π⟩, rfl⟩ := decomposeFin.symm.surjective σ
    intro h
    rw [decomposeFin_symm_apply_succ] at h
    have heq : (π a).succ = p := (swap 0 p).injective (by simpa using h)
    exact ⟨π, by simp [subdivideCycle, heq]⟩

/-- A map that sends each step in a finite permutation orbit to two vertices
of the same target orbit sends the whole orbit into that target orbit. -/
private theorem map_sameCycle {α β : Type*} [Finite α] (f : Perm α) (g : Perm β)
    (map : α → β) (step : ∀ i, g.SameCycle (map i) (map (f i)))
    {x y : α} (h : f.SameCycle x y) : g.SameCycle (map x) (map y) := by
  obtain ⟨k, hk, rfl⟩ := h.exists_pow_eq'
  clear hk h
  induction k with
  | zero => exact SameCycle.rfl
  | succ k ih =>
    rw [pow_succ', mul_apply]
    exact ih.trans (step _)

theorem subdivideCycle_isCycleOn_iff {m : ℕ} (a : Fin m) (π : Perm (Fin m)) :
    (subdivideCycle a π).IsCycleOn Set.univ ↔ π.IsCycleOn Set.univ := by
  let σ := subdivideCycle a π
  let contract : Fin (m + 1) → Fin m := Fin.cases a id
  have hzero : contract 0 = a := rfl
  have hsucc (i : Fin m) : contract i.succ = i := rfl
  have hσ0 : σ 0 = (π a).succ := subdivideCycle_zero a π
  have hσa : σ a.succ = 0 := subdivideCycle_at a π
  have hσaway {i : Fin m} (h : i ≠ a) : σ i.succ = (π i).succ := subdivideCycle_away a π h
  constructor
  · intro h
    refine ⟨π.bijective.bijOn_univ, fun x _ y _ => ?_⟩
    have step (i : Fin (m + 1)) : π.SameCycle (contract i) (contract (σ i)) := by
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hσ0, hzero, hsucc]
        exact SameCycle.rfl.apply_right
      · by_cases hj : j = a
        · subst j
          rw [hσa, hsucc, hzero]
        · rw [hσaway hj, hsucc, hsucc]
          exact SameCycle.rfl.apply_right
    exact map_sameCycle σ π contract step (h.2 (Set.mem_univ x.succ) (Set.mem_univ y.succ))
  · intro h
    have step (i : Fin m) : σ.SameCycle i.succ (π i).succ := by
      by_cases hi : i = a
      · subst i
        rw [← hσ0, ← hσa]
        exact SameCycle.rfl.apply_right.apply_right
      · rw [← hσaway hi]
        exact SameCycle.rfl.apply_right
    have same (i j : Fin m) : σ.SameCycle i.succ j.succ :=
      map_sameCycle π σ Fin.succ step (h.2 (Set.mem_univ i) (Set.mem_univ j))
    have all (i : Fin (m + 1)) : σ.SameCycle a.succ i := by
      refine Fin.cases ?_ (same a) i
      rw [← hσa]
      exact SameCycle.rfl.apply_right
    exact ⟨σ.bijective.bijOn_univ, fun x _ y _ => (all x).symm.trans (all y)⟩

/-- The forced arc from the old root to the new vertex has weight one.
The new outgoing arcs carry the old root's variables except for the
arc back to the root, which is forbidden. -/
def cyclePaddingProjection {m : ℕ} (R : Type*) [CommSemiring R] (a : Fin m)
    : Projection R (Fin (m + 1) × Fin (m + 1)) (Fin m × Fin m) := fun edge =>
  Fin.cases
    (Fin.cases (.inr 0) (fun j => if j = a then .inr 0 else .inl (a, j)))
    (fun i => Fin.cases (if i = a then .inr 1 else .inr 0)
      (fun j => if i = a then .inr 0 else .inl (i, j)))
    edge.1 edge.2

private theorem subdivideCycle_weight {R : Type*} [CommSemiring R] {m : ℕ} (hm : 2 ≤ m)
    (a : Fin m) (π : Equiv.Perm (Fin m)) (hπ : π.IsCycleOn Set.univ) :
    (∏ i, Sum.elim X C (cyclePaddingProjection R a (i, subdivideCycle a π i))) =
      ∏ i, X (i, π i) := by
  classical
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have hne : π a ≠ a := hπ.apply_ne Set.nontrivial_univ (Set.mem_univ a)
  rw [Fin.prod_univ_succ]
  simp only [subdivideCycle_zero, cyclePaddingProjection, Fin.cases_zero, Fin.cases_succ,
    ite_eq_right hne, Sum.elim_inl]
  rw [← Finset.mul_prod_erase Finset.univ (fun i : Fin m => (X (i, π i) :
    MvPolynomial (Fin m × Fin m) R)) (Finset.mem_univ a)]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  simp only [subdivideCycle_at, Fin.cases_zero, ite_true, Sum.elim_inr, map_one, one_mul]
  apply Finset.prod_congr rfl
  intro i hi
  have hia := (Finset.mem_erase.mp hi).1
  simp [subdivideCycle_away a π hia, hia]

/-- Contracting the forced arc projects the polynomial of order `m + 1`
to the polynomial of order `m` over any coefficient semiring. -/
theorem hamiltonianCyclePolynomial_pad {R : Type*} [CommSemiring R] {m : ℕ} (hm : 2 ≤ m)
    (a : Fin m) :
    eval₂Hom C (fun e => Sum.elim X C (cyclePaddingProjection R a e))
      (hamiltonianCyclePolynomial R (m + 1)) = hamiltonianCyclePolynomial R m := by
  classical
  simp only [hamiltonianCyclePolynomial, map_sum, map_prod, eval₂Hom_X']
  have hmpos : 0 < m := by omega
  have subset : (spanningCycles m).image (subdivideCycle a) ⊆ spanningCycles (m + 1) := by
    intro σ hσ
    obtain ⟨π, hπ, rfl⟩ := Finset.mem_image.mp hσ
    simpa [spanningCycles, subdivideCycle_isCycleOn_iff, hmpos] using hπ
  rw [← Finset.sum_subset subset, Finset.sum_image (subdivideCycle_injective a).injOn]
  · apply Finset.sum_congr rfl
    intro π hπ
    exact subdivideCycle_weight hm a π (by simpa [spanningCycles, hmpos] using hπ)
  · intro σ hσ hmiss
    apply Finset.prod_eq_zero (Finset.mem_univ a.succ)
    have hne : σ a.succ ≠ 0 := by
      intro hforced
      obtain ⟨π, rfl⟩ := (range_subdivideCycle a σ).2 hforced
      apply hmiss
      exact Finset.mem_image.mpr ⟨π, by
        simpa [spanningCycles, subdivideCycle_isCycleOn_iff, hmpos] using hσ, rfl⟩
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hne
    simp [← hj, cyclePaddingProjection]


/-- Contraction gives an exact circuit at the smaller order with the same number
of binary gates. -/
theorem Circuit.contract_hamiltonian {R : Type*} [CommRing R] {m k : ℕ} (hm : 2 ≤ m)
    (a : Fin m) (c : Circuit R (Fin (m + 1) × Fin (m + 1)) k)
    (hc : c.polynomial = hamiltonianCyclePolynomial R (m + 1)) :
    (c.subst (cyclePaddingProjection R a) id).polynomial = hamiltonianCyclePolynomial R m := by
  rw [Circuit.project_polynomial, hc]
  exact hamiltonianCyclePolynomial_pad hm a

private theorem spanningCycles_two : spanningCycles 2 = {swap 0 1} := by
  classical
  ext π
  simp only [spanningCycles, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Nat.zero_lt_succ]
  constructor
  · intro h
    ext i
    have hi := h.apply_ne Set.nontrivial_univ (Set.mem_univ i)
    have hv : π i = 0 ∨ π i = 1 := by omega
    rcases hv with hv | hv <;> fin_cases i <;> simp_all
  · rintro rfl
    have h := (isCycle_swap (show (0 : Fin 2) ≠ 1 by decide)).isCycleOn
    convert h using 1
    ext i
    fin_cases i <;> simp

/-- The directed cycle on two vertices consists of its two opposite arcs. -/
theorem hamiltonianCyclePolynomial_two (R : Type*) [CommSemiring R] :
    hamiltonianCyclePolynomial R 2 = X (0, 1) * X (1, 0) := by
  simp [hamiltonianCyclePolynomial, spanningCycles_two, Fin.prod_univ_two]

/-- Keep the first arc and set the other factors to one, as in Section 1.1. -/
def cycleEdgeProjection (R : Type*) [CommRing R] {E : Type*} (e : E) :
    Projection R (Fin 2 × Fin 2) E := fun ij => if ij = (0, 1) then .inl e else .inr 1

theorem cycleEdgeProjection_hamiltonian {R : Type*} [CommRing R] {E : Type*} (e : E) :
    (cycleEdgeProjection R e).hom (hamiltonianCyclePolynomial R 2) = X e := by
  rw [hamiltonianCyclePolynomial_two, map_mul]
  simp [Projection.hom, cycleEdgeProjection]

end VPVNP
end Computability
end OAI
