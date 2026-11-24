import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Nullstellensatz

/-!
# The reduced algebra of a finite geometric slice

Section 8.2 of *VP and VNP differ over every field* takes the quotient of a polynomial
ring over a finite field by the ideal vanishing at all geometric points of a finite slice.
Evaluation embeds this reduced coordinate algebra in the functions on the slice. The
points can be defined over an extension field. Frobenius permutes the points and forces
the coefficients of every minimal linear dependence to descend to the base field.
This bounds the base-field dimension by the number of geometric points.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace FiniteSlice

open Polynomial MvPolynomial

/-- A coordinate fixed by the cardinality Frobenius of the ground field descends to that field. -/
theorem exists_algebraMap_eq_of_frobenius_fixed (K : Type*) {E : Type*}
    [Field K] [Fintype K] [Field E] [Algebra K E] {x : E}
    (hx : FiniteField.frobeniusAlgHom K E x = x) : ∃ c : K, algebraMap K E c = x := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hs : (Polynomial.X ^ Fintype.card K - Polynomial.X : K[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      ← Finset.card_def, Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq K hq]
  apply hs.mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero K hq)
  simpa [IsRoot.def, sub_eq_zero] using hx

/-- A finite family of functions equivariant for a permutation of the arguments and
a field endomorphism is linearly independent over the extension whenever it is
linearly independent over the fixed field. -/
theorem linearIndependent_of_fixedField
    {K E α : Type*} [Field K] [Field E] [Algebra K E]
    (σ : E →ₐ[K] E) (hfixed : ∀ x, σ x = x → ∃ c : K, algebraMap K E c = x)
    (e : Equiv.Perm α) {n : ℕ} (f : Fin n → α → E)
    (hf : ∀ i a, f i (e a) = σ (f i a)) (hK : LinearIndependent K f) :
    LinearIndependent E f := by
  classical
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
    obtain ⟨hinit, hlast⟩ := linearIndependent_finSucc'.mp hK
    have hE : LinearIndependent E (Fin.init f) :=
      ih (Fin.init f) (fun i a ↦ hf i.castSucc a) hinit
    refine linearIndependent_finSucc'.mpr ⟨hE, fun hspan ↦ hlast ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hspan
    have hpoint (a : α) : ∑ i, c i * f i.castSucc a = f (Fin.last n) a := by
      simpa [Finset.sum_apply, Fin.init, Pi.smul_apply, smul_eq_mul] using congrFun hc a
    have hconj : ∑ i, σ (c i) • Fin.init f i = f (Fin.last n) := by
      funext a
      obtain ⟨b, rfl⟩ := e.surjective a
      simpa [Finset.sum_apply, Fin.init, Pi.smul_apply, smul_eq_mul, hf, map_sum, map_mul]
        using congrArg σ (hpoint b)
    have hcfix (i : Fin n) : σ (c i) = c i := hE.eq_coords_of_eq (hconj.trans hc.symm) i
    choose d hd using fun i ↦ hfixed (c i) (hcfix i)
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨d, ?_⟩
    simpa only [← hd, algebraMap_smul] using hc

/-- A finite coordinate model preserving independence after extending scalars bounds
the dimension over the original field. -/
theorem finite_and_finrank_le_of_independence
    {K E R α : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup R] [Module K R] [Fintype α]
    (inj : R →ₗ[K] (α → E))
    (h : ∀ (n : ℕ) (f : Fin n → R), LinearIndependent K f →
      LinearIndependent E (fun i => inj (f i))) :
    Module.Finite K R ∧ Module.finrank K R ≤ Fintype.card α := by
  classical
  have hRank : Module.rank K R ≤ Fintype.card α := by
    apply rank_le
    intro s hs
    let e := (Finset.equivFinOfCardEq (s := s) rfl).symm
    have hi := h s.card (fun i => (e i : R)) ((linearIndependent_equiv e).mpr hs)
    simpa only [Fintype.card_fin, Module.finrank_pi] using hi.fintype_card_le_finrank
  exact ⟨Module.rank_lt_aleph0_iff.mp (hRank.trans_lt Cardinal.natCast_lt_aleph0),
    Module.finrank_le_of_rank_le hRank⟩

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

/-- The reduced coordinate algebra over the base field of a set of extension-field points. -/
abbrev CoordinateAlgebra (K : Type*) [Field K] [Algebra K E] (V : Set (ι → E)) :=
  MvPolynomial ι K ⧸ vanishingIdeal K V

/-- The images of the polynomial variables in the slice algebra. -/
noncomputable def coordinateLabel (V : Set (ι → E)) (i : ι) : CoordinateAlgebra K V :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem aeval_coordinateLabel (V : Set (ι → E)) :
    MvPolynomial.aeval (coordinateLabel (K := K) V) = Ideal.Quotient.mkₐ K (vanishingIdeal K V) := by
  ext i
  rw [MvPolynomial.aeval_X]
  rfl

theorem adjoin_coordinateLabel (V : Set (ι → E)) :
    Algebra.adjoin K (Set.range (coordinateLabel (K := K) V)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, aeval_coordinateLabel, AlgHom.range_eq_top]
  exact Ideal.Quotient.mk_surjective

/-- Evaluation of classes of base-field polynomials at all points of the slice. -/
noncomputable def sliceEvaluation (V : Set (ι → E)) :
    CoordinateAlgebra K V →ₐ[K] (V → E) :=
  Ideal.Quotient.liftₐ (vanishingIdeal K V) (AlgHom.pi fun x : V => aeval x.val)
    fun _ hp => funext fun x => hp x.val x.property

@[simp] theorem sliceEvaluation_mk (V : Set (ι → E)) (p : MvPolynomial ι K) (x : V) :
    sliceEvaluation V (Ideal.Quotient.mk _ p) x = aeval x.val p := rfl

theorem sliceEvaluation_injective (V : Set (ι → E)) :
    Function.Injective (sliceEvaluation (K := K) V) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := vanishingIdeal K V) a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := vanishingIdeal K V) b
  apply Ideal.Quotient.eq.mpr
  intro x hx
  rw [map_sub, sub_eq_zero]
  exact congrFun hab ⟨x, hx⟩

theorem coordinateAlgebra_isReduced (V : Set (ι → E)) :
    IsReduced (CoordinateAlgebra K V) :=
  isReduced_of_injective (sliceEvaluation V) (sliceEvaluation_injective V)

theorem coordinateAlgebra_nontrivial (V : Set (ι → E)) [Nonempty V] :
    Nontrivial (CoordinateAlgebra K V) :=
  (sliceEvaluation (K := K) V).toRingHom.domain_nontrivial

/-- Every original label equation holds in the reduced coordinate algebra. -/
theorem equation_eq_zero (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) (hp : p ∈ I) :
    Ideal.Quotient.mk (vanishingIdeal K (zeroLocus E I)) p = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (le_vanishingIdeal_zeroLocus I hp)

private def mapPoint (I : Ideal (MvPolynomial ι K)) (σ : E →ₐ[K] E) (x : zeroLocus E I) :
    zeroLocus E I :=
  ⟨fun i => σ (x.val i), fun p hp => by
    rw [← comp_aeval_apply, x.property p hp, map_zero]⟩

/-- A field endomorphism fixing the coefficient field permutes the points of a finite slice. -/
noncomputable def pointPerm (I : Ideal (MvPolynomial ι K)) [Finite (zeroLocus E I)]
    (σ : E →ₐ[K] E) : Equiv.Perm (zeroLocus E I) :=
  Equiv.ofBijective (mapPoint I σ) <| Finite.injective_iff_bijective.mp fun _ _ h =>
    Subtype.ext <| funext fun i => σ.injective (congrFun (congrArg Subtype.val h) i)

theorem sliceEvaluation_equivariant (I : Ideal (MvPolynomial ι K)) [Finite (zeroLocus E I)]
    (σ : E →ₐ[K] E) (a : CoordinateAlgebra K (zeroLocus E I)) (x : zeroLocus E I) :
    sliceEvaluation _ a (pointPerm I σ x) = σ (sliceEvaluation _ a x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := vanishingIdeal K _) a
  exact (comp_aeval_apply x.val σ p).symm

/-- Dimension bound for a finite slice defined by base-field equations.
The extension `E` may be the algebraic closure of `K`. -/
theorem coordinateAlgebra_finite_finrank [Fintype K] (I : Ideal (MvPolynomial ι K))
    [Fintype (zeroLocus E I)] :
    Module.Finite K (CoordinateAlgebra K (zeroLocus E I)) ∧
      Module.finrank K (CoordinateAlgebra K (zeroLocus E I)) ≤ Fintype.card (zeroLocus E I) := by
  let eval := sliceEvaluation (K := K) (zeroLocus E I)
  let σ := FiniteField.frobeniusAlgHom K E
  apply finite_and_finrank_le_of_independence eval.toLinearMap
  intro n f hf
  apply linearIndependent_of_fixedField σ (fun _ h => exists_algebraMap_eq_of_frobenius_fixed K h)
    (pointPerm I σ) _ (fun i x => sliceEvaluation_equivariant I σ (f i) x)
  exact hf.map' eval.toLinearMap
    (LinearMap.ker_eq_bot_of_injective (sliceEvaluation_injective _))

end FiniteSlice

end VPVNP
end Computability
end OAI
