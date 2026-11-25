import OAI.Computability.BorderVNP.ResidueFourier
import OAI.Computability.BorderVNP.BranchGridExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Evaluating the matrix-entry interpolation summands

For the specific product in (10.3), a grid summand only evaluates the input chart
equations, monomials, and powers in a finite field. The extraction includes the
zero case when the requested exponent falls outside the shifted interval.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open ResidueBox
open scoped BigOperators Classical

variable {σ ι E K : Type*} [Fintype σ] [Fintype ι] [Field E] [Field K]

private def gridCharacter (x : Option σ → Kˣ) : Multiplicative (Exponent σ) →* K where
  toFun a := monomialValue x a.toAdd
  map_one' := by simp [monomialValue]
  map_mul' a b := by
    change (∏ i, (x i : K) ^ (a.toAdd i + b.toAdd i)) = _
    simp only [zpow_add₀ (Units.ne_zero _), Finset.prod_mul_distrib]
    rfl

private noncomputable def gridHom (φ : E →+* K) (x : Option σ → Kˣ) : Laurent σ E →+* K :=
  AddMonoidAlgebra.liftNCRingHom φ (gridCharacter x) fun _ _ => Commute.all _ _

private theorem gridHom_toLaurent (φ : E →+* K) (x : Option σ → Kˣ) :
    (gridHom φ x).comp toLaurent = MvPolynomial.eval₂Hom φ (fun i => (x i : K)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [MvPolynomial.eval₂Hom_C]
    change gridHom φ x (AddMonoidAlgebra.mapDomain (polynomialExponents _) (.single 0 c)) = φ c
    simp [gridHom, gridCharacter, monomialValue]
  · intro k
    rw [MvPolynomial.eval₂Hom_X']
    change gridHom φ x (AddMonoidAlgebra.mapDomain (polynomialExponents _)
      (.single (Finsupp.single k 1) 1)) = (x k : K)
    simp only [AddMonoidAlgebra.mapDomain_single, gridHom, AddMonoidAlgebra.liftNCRingHom_single,
      map_one, one_mul, gridCharacter, MonoidHom.coe_mk, OneHom.coe_mk, monomialValue,
      polynomialExponents, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toAdd_ofAdd]
    rw [Finset.prod_eq_single k]
    · simp
    · intro j _ hj
      simp [Finsupp.single_eq_of_ne hj]
    · simp

/-- Evaluation of the source product by evaluating its chart factors separately. -/
theorem gridValue_source_product (φ : E →+* K) (x : Option σ → Kˣ) (q : ℕ)
    (g : ι → MvPolynomial (Option σ) E) (e : Exponent σ) (b : E) :
    gridValue φ (AddMonoidAlgebra.single e b * equationProduct q g).coeff x =
      (φ b * monomialValue x e) * ∏ k, (MvPolynomial.eval₂ φ (fun i => (x i : K)) (g k)) ^
        (q - 1) := by
  change gridHom φ x (AddMonoidAlgebra.single e b * toLaurent (∏ k, g k ^ (q - 1))) = _
  rw [map_mul, ← RingHom.comp_apply, gridHom_toLaurent, map_prod]
  simp only [map_pow, gridHom, AddMonoidAlgebra.liftNCRingHom_single, gridCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rfl

/-- Membership in the exact interval where the unextracted coefficient may be nonzero. -/
def inShiftedBox (e j : Exponent σ) (width : ℕ) : Prop :=
  ∀ i, e i ≤ j i ∧ j i ≤ e i + width

variable [Fintype K]

/-- The actual §10.2 coefficient reader. The tests use the identity as inverse Frobenius
when the extraction power is a power of the coefficient-field cardinality. -/
theorem entry_on_grid (φ : E →+* K) (q : ℕ) (hq : 0 < q) (g : ι → MvPolynomial (Option σ) E)
    (a b : E) (e μ k : Exponent σ)
    (hwidth : (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ) :
    let j := sourceIndex q (k - μ)
    let width := (q - 1) * ∑ t, (g t).totalDegree
    φ ((rowPolynomial q hq g (RingHom.id E) a b e μ).coeff k) =
      if inShiftedBox e j width then
        φ a * (((Fintype.card Kˣ : K) ^ Fintype.card (Option σ))⁻¹ *
          ∑ x : Option σ → Kˣ, ((φ b * monomialValue x e) *
            ∏ t, (MvPolynomial.eval₂ φ (fun i => (x i : K)) (g t)) ^ (q - 1)) *
            monomialValue x (-j))
      else 0 := by
  classical
  dsimp only
  let V := AddMonoidAlgebra.single e b * equationProduct q g
  let j := sourceIndex q (k - μ)
  let w := (q - 1) * ∑ t, (g t).totalDegree
  have bounds (s : Exponent σ) (hs : s ∈ V.coeff.support) : inShiftedBox e s w := by
    obtain ⟨f, hf, h⟩ := before_extraction_bounds q g (.single e b) hs
    have : f = e := Finset.mem_singleton.mp (Finsupp.support_single_subset hf)
    rw [this] at h
    exact h
  rw [rowPolynomial_coeff, RingHom.id_apply, map_mul]
  change φ a * φ (V.coeff j) = if inShiftedBox e j w then _ else 0
  by_cases hj : inShiftedBox e j w
  · rw [ite_eq_left hj, coefficient_on_box φ V.coeff j e w hwidth hj bounds]
    simp_rw [V, gridValue_source_product]
    congr 2
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro x _
    rfl
  · have hzero : V.coeff j = 0 :=
      Finsupp.notMem_support_iff.mp fun h => hj (bounds j h)
    rw [ite_eq_right hj, hzero, map_zero, mul_zero]

/-- A single interpolation field inside the algebraic closure works for all translated boxes
of width at most the requested width. Its cardinality has a multiplicative upper bound. -/
theorem exists_interpolation_field (E : Type*) [Field E] [Fintype E] (width : ℕ) :
    ∃ K : IntermediateField E (AlgebraicClosure E), Finite K ∧
      width < Nat.card Kˣ ∧ Nat.card K ≤ Fintype.card E * (width + 1) := by
  obtain ⟨K, hfinite, hlarge, hsmall⟩ :=
    Branch.exists_gridExtension E (AlgebraicClosure E) (width + 1)
  refine ⟨K, hfinite, ?_, ?_⟩
  · rw [Nat.card_units]
    omega
  · simpa only [max_eq_left (Nat.le_add_left 1 width)] using hsmall

end ResidueFourier

end BorderVNP
end Computability
end OAI
