import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.RingTheory.Unramified.Field

/-!
# Separability at a generically nonsingular square system

Over the field of the deformation parameter, the Jacobian of the square
system annihilates the derivatives of the parameter coordinates. Its
nonvanishing forces every relative derivation on the generated function
field to be zero. Thus the extension is finite and separable, in positive
characteristic as well as in characteristic zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped BigOperators Matrix

private theorem scalar_chain_rule {F L ι : Type*} [Field F] [Field L] [Algebra F L]
    [Fintype ι] (D : Derivation F L L) (x : ι → L) (p : MvPolynomial ι F) :
    D (aeval x p) = ∑ i, aeval x (pderiv i p) * D (x i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, D.leibniz, pderiv_mul, pderiv_X, map_add, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, hp]
    simp [Pi.single_apply, apply_ite, mul_assoc, mul_left_comm, Finset.mul_sum, add_comm]

/-- At a root of a generically nonsingular square system, the field generated
by the root coordinates is finite separable over the coefficient field.
In (9.1) the coefficient field is the rational function field in `t`. -/
theorem finite_separable_of_nonsingular_system {F L ι : Type*}
    [Field F] [Field L] [Algebra F L] [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial ι F) (x : ι → L)
    (hgen : IntermediateField.adjoin F (Set.range x) = ⊤)
    (hzero : ∀ i, aeval x (g i) = 0)
    (hjac : (Matrix.of fun i j => aeval x (pderiv j (g i))).det ≠ 0) :
    FiniteDimensional F L ∧ Algebra.IsSeparable F L := by
  classical
  have annihilates (D : Derivation F L L) (a : L) : D a = 0 := by
    let J := Matrix.of fun i j => aeval x (pderiv j (g i))
    have hdx : D ∘ x = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero (M := J) hjac
      funext i
      change (∑ j, aeval x (pderiv j (g i)) * D (x j)) = 0
      rw [← scalar_chain_rule, hzero, map_zero]
    have ha : a ∈ IntermediateField.adjoin F (Set.range x) := hgen ▸ trivial
    refine IntermediateField.adjoin_induction F (p := fun b _ => D b = 0)
      (fun b hb => ?_) (D.map_algebraMap) (fun b c _ _ hb hc => ?_)
      (fun b _ hb => ?_) (fun b c _ _ hb hc => ?_) ha
    · obtain ⟨i, rfl⟩ := hb
      exact congrFun hdx i
    · rw [map_add, hb, hc, add_zero]
    · rw [D.leibniz_inv, hb, smul_zero]
    · rw [D.leibniz, hb, hc, smul_zero, smul_zero, add_zero]
  have : Algebra.FormallyUnramified F L := by
    constructor
    suffices (⊤ : Submodule L (KaehlerDifferential F L)) ≤ ⊥ from
      (subsingleton_iff_forall_eq 0).mpr fun a => this trivial
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    apply (Module.forall_dual_apply_eq_zero_iff L _).mp
    intro φ
    exact annihilates (φ.compDer (KaehlerDifferential.D F L)) a
  have : Algebra.EssFiniteType F L := IntermediateField.fg_top_iff.mp
    ⟨Finset.univ.image x, by simpa using hgen⟩
  exact ⟨Algebra.FormallyUnramified.finite_of_free F L, Algebra.FormallyUnramified.isSeparable F L⟩

end Branch

end BorderVNP
end Computability
end OAI
