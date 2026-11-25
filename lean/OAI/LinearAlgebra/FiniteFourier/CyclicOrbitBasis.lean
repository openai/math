import OAI.LinearAlgebra.FiniteFourier.CyclicEigenbasis

/-! # Fourier bases of free cyclic orbits

On a basis consisting of cycles of the same length, Fourier transformation
gives one basis vector from each orbit in each eigenspace. Two orbits give
the pair of vectors in the prime-axis construction.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Module Submodule
open scoped BigOperators

variable {R M C : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ}

/-- Fourier vector on the orbit `c` at the frequency `j`. -/
noncomputable def orbitFourier (b : Basis (C × Fin m) R M) (u : Rˣ) (c : C) (j : Fin m) : M :=
  ∑ t : Fin m, (↑((u^j.val)⁻¹) : R)^t.val • b (c,t)

/-- A linear map carrying one cycle to another carries their Fourier
vectors into one another. In particular the prime-axis involution swaps them. -/
theorem map_orbitFourier (b : Basis (C × Fin m) R M) (u : Rˣ) (τ : Module.End R M)
    {c c' : C} (ht : ∀ t, τ (b (c,t)) = b (c',t)) (j : Fin m) :
    τ (orbitFourier b u c j) = orbitFourier b u c' j := by
  simp only [orbitFourier, map_sum, map_smul, ht]

theorem orbitFourier_eq_sum (b : Basis (C × Fin m) R M) (u : Rˣ) (σ : Module.End R M)
    (v : C → M) (horbit : ∀ c (t : Fin m), (σ^t.val) (v c) = b (c,t))
    (c : C) (j : Fin m) :
    orbitFourier b u c j = cyclicSpectralSum σ u m j.val (v c) := by
  simp only [orbitFourier, cyclicSpectralSum, LinearMap.sum_apply, LinearMap.smul_apply, horbit]

theorem orbitFourier_eigen (b : Basis (C × Fin m) R M) (u : Rˣ) (σ : Module.End R M)
    (hu : u^m = 1) (hσ : σ^m = 1)
    (v : C → M) (horbit : ∀ c (t : Fin m), (σ^t.val) (v c) = b (c,t))
    (c : C) (j : Fin m) :
    σ (orbitFourier b u c j) = (u:R)^j.val • orbitFourier b u c j := by
  rw [orbitFourier_eq_sum b u σ v horbit]
  exact LinearMap.congr_fun (cyclicSpectralSum_eigen _ _ hσ hu) _

private theorem orbitFourier_coord_zero [DecidableEq C] (b : Basis (C × Fin m) R M) (u : Rˣ)
    (hmpos : 0 < m) (c c' : C) (j : Fin m) :
    b.coord (c,⟨0,hmpos⟩) (orbitFourier b u c' j) = if c' = c then 1 else 0 := by
  classical
  simp only [orbitFourier, map_sum, map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single (⟨0,hmpos⟩ : Fin m)]
  · simp [Prod.ext_iff]
  · intro t _ ht
    simp [Prod.ext_iff, ht]
  · simp

variable [Fintype C]

/-- The orbit Fourier vectors form a basis simultaneously across all the
orbits and frequencies. -/
theorem exists_orbitFourier_basis (b : Basis (C × Fin m) R M) (u : Rˣ) (σ : Module.End R M)
    (hmpos : 0 < m) (hm : IsUnit (m:R)) (hu : u^m = 1) (hσ : σ^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (v : C → M) (horbit : ∀ c (t : Fin m), (σ^t.val) (v c) = b (c,t)) :
    ∃ e : Basis (C × Fin m) R M, ∀ c j, e (c,j) = orbitFourier b u c j := by
  classical
  let γ (a : C × Fin m) := orbitFourier b u a.1 a.2
  have hγ (a : C × Fin m) := orbitFourier_eigen b u σ hu hσ v horbit a.1 a.2
  have hli : LinearIndependent R γ := by
    apply Fintype.linearIndependent_iff.mpr
    intro f hf a
    obtain ⟨c,j⟩ := a
    let row := (b.coord (c,⟨0,hmpos⟩)).comp (cyclicProjector σ u hm j)
    have hrow (a : C × Fin m) : row (γ a) = if a = (c,j) then 1 else 0 := by
      obtain ⟨c',j'⟩ := a
      change (b.coord _) (cyclicProjector σ u hm j (orbitFourier b u c' j')) = _
      rw [cyclicProjector_apply_eigen σ u hu hm hs _ _ _ (hγ (c',j'))]
      by_cases hj : j = j'
      · subst j'
        simpa [Prod.ext_iff] using orbitFourier_coord_zero b u hmpos c c' j
      · simp [hj, Ne.symm hj, Prod.ext_iff]
    have he := congrArg row hf
    simpa only [map_sum, map_smul, map_zero, hrow, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he
  have hsp : ⊤ ≤ span R (Set.range γ) := by
    rw [← b.span_eq]
    apply span_le.mpr
    rintro x ⟨⟨c,t⟩,rfl⟩
    have he := LinearMap.congr_fun (sum_cyclicProjector σ u hmpos hu hm hs) (v c)
    simp only [LinearMap.sum_apply, cyclicProjector, LinearMap.smul_apply, Module.End.one_apply,
      ← orbitFourier_eq_sum b u σ v horbit] at he
    rw [← horbit c t, ← he, map_sum]
    apply sum_mem
    intro j _
    rw [map_smul]
    apply smul_mem
    have hpow (k : ℕ) : (σ^k) (γ (c,j)) = ((u:R)^j.val)^k • γ (c,j) := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hγ (c,j), smul_smul, pow_succ]
    change (σ^t.val) (γ (c,j)) ∈ _
    rw [hpow]
    exact smul_mem _ _ (subset_span ⟨(c,j),rfl⟩)
  exact ⟨Basis.mk hli hsp, fun _ _ => Basis.mk_apply _ _ _⟩

/-- The vectors at one frequency span exactly that eigenspace. Thus when
there are two cyclic orbits the two displayed vectors give its basis. -/
theorem eigenspace_eq_span_orbitFourier (b : Basis (C × Fin m) R M) (u : Rˣ)
    (σ : Module.End R M) (hmpos : 0 < m) (hm : IsUnit (m:R)) (hu : u^m = 1) (hσ : σ^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))
    (v : C → M) (horbit : ∀ c (t : Fin m), (σ^t.val) (v c) = b (c,t)) (j : Fin m) :
    σ.eigenspace ((u:R)^j.val) = span R (Set.range (fun c => orbitFourier b u c j)) := by
  obtain ⟨e, he⟩ := exists_orbitFourier_basis b u σ hmpos hm hu hσ hs v horbit
  have heig (c : C) (i : Fin m) := orbitFourier_eigen b u σ hu hσ v horbit c i
  apply le_antisymm
  · intro x hx
    have hPx := cyclicProjector_apply_eigen σ u hu hm hs j j x (Module.End.mem_eigenspace_iff.mp hx)
    simp only [ite_true] at hPx
    have hexp := congrArg (cyclicProjector σ u hm j) (e.sum_repr x)
    rw [hPx, map_sum] at hexp
    rw [← hexp]
    apply sum_mem
    rintro ⟨c,i⟩ _
    rw [map_smul, he, cyclicProjector_apply_eigen σ u hu hm hs j i _ (heig c i)]
    apply smul_mem
    split_ifs with h
    · subst i
      exact subset_span ⟨c,rfl⟩
    · exact zero_mem _
  · apply span_le.mpr
    rintro x ⟨c,rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (heig c j)

end FiniteFourier
end LinearAlgebra
end OAI
