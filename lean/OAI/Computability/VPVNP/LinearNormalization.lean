import OAI.Computability.VPVNP.LinearNormalizationDimension
import OAI.Computability.VPVNP.LinearNormalizationStep
import OAI.Computability.VPVNP.LinearNormalizationTower

/-!
# Noether normalization by linear combinations of specified generators

Over an infinite field, a dependent tuple admits a linear shear after
which one generator can be removed while preserving integrality. Repeating
this reduction gives an independent tuple in the linear span of the
original one. In a polynomial algebra the length of the tuple is its
number of variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LinearNormalization

open MvPolynomial

variable {K A : Type*} [Field K] [Infinite K] [CommRing A] [Nontrivial A] [Algebra K A]

/-- Linear normalization for a tuple whose generated subalgebra has an integral
extension to the whole ambient algebra. -/
theorem exists_of_integral_adjoin {n : ℕ} (g : Fin n → A)
    (hg : ∀ a : A, IsIntegral (Algebra.adjoin K (Set.range g)) a) :
    ∃ (s : ℕ) (Q : Fin s → A),
      (∀ j, Q j ∈ Submodule.span K (Set.range g)) ∧
      Function.Injective (aeval Q : MvPolynomial (Fin s) K →ₐ[K] A) ∧
      ∀ a : A, IsIntegral (Algebra.adjoin K (Set.range Q)) a := by
  induction n with
  | zero =>
    refine ⟨0, g, fun j => j.elim0, ?_, hg⟩
    intro p q he
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at he ⊢
    exact congrArg C ((algebraMap K A).injective (by simpa only [aeval_C] using he))
  | succ n ih =>
    by_cases hi : Function.Injective (aeval g : MvPolynomial (Fin (n + 1)) K →ₐ[K] A)
    · exact ⟨n + 1, g, fun j => Submodule.subset_span ⟨j, rfl⟩, hi, hg⟩
    obtain ⟨v, hv⟩ := exists_integral_shear g hi
    let g' (j : Fin n) := g j.succ - v j • g 0
    obtain ⟨s, Q, hQ, hinj, hint⟩ := ih g' (fun a =>
      integral_over_new_generators (Algebra.adjoin K (Set.range g')) g hv a (hg a))
    refine ⟨s, Q, fun j => ?_, hinj, hint⟩
    have hle : Submodule.span K (Set.range g') ≤ Submodule.span K (Set.range g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨i.succ, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    exact hle (hQ j)

/-- An explicitly generated polynomial algebra in `m` variables has an integral
normalization by exactly `m` linear combinations of the given generators. -/
theorem exists_linear_normalization {m : ℕ} {I : Type*} [Fintype I]
    (g : I → MvPolynomial (Fin m) K) (hg : Algebra.adjoin K (Set.range g) = ⊤) :
    ∃ Q : Fin m → MvPolynomial (Fin m) K,
      (∀ j, Q j ∈ Submodule.span K (Set.range g)) ∧
      Function.Injective (aeval Q : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) ∧
      ∀ p : MvPolynomial (Fin m) K, IsIntegral (aeval Q : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K).range p := by
  let g' := g ∘ (Fintype.equivFin I).symm
  have hr : Set.range g' = Set.range g := (Fintype.equivFin I).symm.surjective.range_comp g
  have hgi (p : MvPolynomial (Fin m) K) : IsIntegral (Algebra.adjoin K (Set.range g')) p := by
    let t : Algebra.adjoin K (Set.range g') := ⟨p, by rw [hr, hg]; trivial⟩
    exact isIntegral_algebraMap (x := t)
  obtain ⟨s, Q, hspan, hinj, hint⟩ := exists_of_integral_adjoin g' hgi
  let f : MvPolynomial (Fin s) K →ₐ[K] MvPolynomial (Fin m) K := aeval Q
  have h : ∀ p : MvPolynomial (Fin m) K, IsIntegral f.range p := by
    have hrange : Algebra.adjoin K (Set.range Q) = f.range := Algebra.adjoin_range_eq_range_aeval K Q
    exact hrange ▸ hint
  have hsm := numVars_eq_of_integral_injective f hinj ((isIntegral_iff_range f).2 h)
  subst s
  exact ⟨Q, fun j => hr ▸ hspan j, hinj, h⟩

end LinearNormalization

end VPVNP
end Computability
end OAI
