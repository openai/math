import OAI.LinearAlgebra.FiniteFourier.CyclicOrbitBasis
import Mathlib.Algebra.DirectSum.Module

/-! # Frequency blocks in the two-orbit prime-axis change of basis

A basis of eigenvectors determines an internal sum of the frequency modules.
Their bases can therefore be changed independently. The off-frequency
coordinates vanish in both directions over rings with separated roots.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Module Submodule

variable {R M T C : Type*} [CommRing R] [AddCommGroup M] [Module R M] {m : ℕ}

/-- The frequency modules of a split cyclic action give an internal direct sum. -/
theorem cyclicEigen_isInternal (σ : Module.End R M) (u : Rˣ)
    (hu : u ^ m = 1) (hm : IsUnit (m : R))
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u : R)^i.val - (u : R)^j.val))
    (b : Basis (C × Fin m) R M)
    (hb : ∀ c j, σ (b (c,j)) = (u : R)^j.val • b (c,j)) :
    DirectSum.IsInternal (fun j : Fin m => σ.eigenspace ((u : R)^j.val)) := by
  classical
  let E (j : Fin m) := σ.eigenspace ((u : R)^j.val)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    let P := cyclicProjector σ u hm i
    have hk : (⨆ (j : Fin m) (_ : j ≠ i), E j) ≤ P.ker := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      apply LinearMap.mem_ker.mpr
      exact (cyclicProjector_apply_eigen σ u hu hm hs i j y
        (Module.End.mem_eigenspace_iff.mp hy)).trans (ite_eq_right hj.symm)
    have hfix := cyclicProjector_apply_eigen σ u hu hm hs i i x
      (Module.End.mem_eigenspace_iff.mp hx)
    exact (show P x = x by simpa [P] using hfix).symm.trans (LinearMap.mem_ker.mp (hk hy))
  · apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨c,j⟩,rfl⟩
    exact (le_iSup E j) (Module.End.mem_eigenspace_iff.mpr (hb c j))

/-- Collecting a basis from each frequency yields the Cartesian-indexed global basis. -/
theorem exists_cyclicEigen_basis (σ : Module.End R M) (u : Rˣ)
    (hu : u ^ m = 1) (hm : IsUnit (m : R))
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u : R)^i.val - (u : R)^j.val))
    (b : Basis (C × Fin m) R M)
    (hb : ∀ c j, σ (b (c,j)) = (u : R)^j.val • b (c,j))
    (v : ∀ j : Fin m, Basis T R (σ.eigenspace ((u : R)^j.val))) :
    ∃ e : Basis (T × Fin m) R M, ∀ t j, e (t,j) = (v j t : M) := by
  classical
  let h := cyclicEigen_isInternal σ u hu hm hs b hb
  let equiv := (Equiv.sigmaEquivProd (Fin m) T).trans (Equiv.prodComm _ _)
  exact ⟨(h.collectedBasis v).reindex equiv, fun t j => by
    rw [Basis.reindex_apply, DirectSum.IsInternal.collectedBasis_coe]; rfl⟩

/-- Coordinates of an eigenvector vanish in rows belonging to other frequencies.
Applying this to either basis proves that both basis changes are block diagonal. -/
theorem eigenBasis_repr_eq_zero {ι κ : Type*} (σ : Module.End R M) (val : κ → R)
    (hs : ∀ i j, i ≠ j → IsUnit (val i - val j)) (freq : ι → κ)
    (b : Basis ι R M) (hb : ∀ a, σ (b a) = val (freq a) • b a)
    {j : κ} (a : ι) (hja : j ≠ freq a) {x : M} (hx : σ x = val j • x) :
    b.repr x a = 0 := by
  classical
  let row := b.coord a
  have hr : row.comp σ = val (freq a) • row := by
    apply b.ext
    intro i
    by_cases he : i = a
    · subst i
      simp [row, hb]
    · simp [row, hb, Basis.coord_apply, Basis.repr_self, he]
  have h := LinearMap.congr_fun hr x
  change row (σ x) = val (freq a) * row x at h
  rw [hx, map_smul, smul_eq_mul] at h
  apply (hs j (freq a) hja).mul_right_eq_zero.mp
  exact (sub_mul _ _ _).trans (sub_eq_zero.mpr h)

end FiniteFourier
end LinearAlgebra
end OAI
