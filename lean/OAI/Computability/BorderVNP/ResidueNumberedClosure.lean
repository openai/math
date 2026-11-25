import OAI.Computability.BorderVNP.ResidueNumberedQuery

/-!
# Variable numbering before the border construction

Bijective renaming reorders the coefficient space, including all nonsquarefree
monomials, and reuses precisely the original shared arithmetic gates. It
therefore commutes with degree-component closure at the same gate budget.
This gives the §9.2 input directly from the border hypothesis for the signed
polynomial in paired variables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

variable {V W K : Type*} [Field K]

private noncomputable def pullIndex (e : V ≃ W) (d : ℕ) (i : DegreeMonomial W d) : DegreeMonomial V d :=
  ⟨i.val.mapDomain e.symm, (Finsupp.degree_mapDomain _ _).trans i.property⟩

private theorem pull_coeff (e : V ≃ W) (d : ℕ) (P : MvPolynomial V K) (i : DegreeMonomial W d) :
    coeffVector d (rename e P) i = coeffVector d P (pullIndex e d i) := by
  have he : (i.val.mapDomain e.symm).mapDomain e = i.val := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  change (rename e P).coeff i.val = P.coeff (i.val.mapDomain e.symm)
  simpa only [he] using coeff_rename_mapDomain e e.injective P (i.val.mapDomain e.symm)

/-- Reordering variables transports the affine image closure at the same gate count. -/
theorem geometricApprox_rename_equiv (e : V ≃ W) {d s : ℕ} {P : MvPolynomial V K}
    (h : geometricApprox d s P) : geometricApprox d s (rename e P) := by
  let f (i : DegreeMonomial W d) : MvPolynomial (DegreeMonomial V d) K := X (pullIndex e d i)
  have hc := imageClosure_polynomial h f
  unfold geometricApprox
  rw [show coeffVector d (rename e P) = (fun i => eval (coeffVector d P) (f i)) from
    funext fun i => (pull_coeff e d P i).trans (eval_X _).symm]
  refine imageClosure_mono ?_ hc
  rintro _ ⟨_, ⟨m, hm, c, rfl⟩, rfl⟩
  let proj : VPVNP.Projection K V W := fun i => .inl (e i)
  have hp : proj.hom = (rename (R := K) e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [VPVNP.Projection.hom]
    · intro i
      simp [VPVNP.Projection.hom, proj]
  exact ⟨m, hm, c.subst proj id, by
    rw [VPVNP.Circuit.project_polynomial, hp]
    exact funext fun i => (pull_coeff e d c.polynomial i).trans (eval_X _).symm⟩

/-- Bijective numbering gives equivalent degree-component border approximations. -/
theorem borderApprox_rename_equiv_iff (e : V ≃ W) (d s : ℕ) (P : MvPolynomial V K) :
    BorderApprox d s (rename e P) ↔ BorderApprox d s P := by
  unfold BorderApprox
  rw [map_rename]
  constructor
  · intro h
    have h' := geometricApprox_rename_equiv e.symm h
    simpa only [rename_rename, Equiv.symm_comp_self, rename_id, AlgHom.id_apply] using h'
  · exact geometricApprox_rename_equiv e

/-- The full numbered-table closure needed to specialize the signed family. -/
theorem numbered_signed_tableClosure {F : Type*} [Field F] (k s : ℕ)
    (e : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (h : BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1)))) :
    Int.castRingHom (AlgebraicClosure F) ∘ coeffVector (k+1) (rename e (Pstar (k+1))) ∈
      imageClosure (BranchSpecialization.polynomialImage
        (Branch.numberedTable (AlgebraicClosure F) (2*(k+1)) k s)) := by
  apply Branch.numbered_table_closure_of_borderApprox
  rw [map_rename, borderApprox_rename_equiv_iff]
  exact h

end BorderVNP
end Computability
end OAI
