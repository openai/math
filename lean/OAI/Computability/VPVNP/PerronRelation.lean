import OAI.Computability.VPVNP.PerronSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Perron's quantitative algebraic-dependence argument

Substitute the given polynomials into a finite family of distinct monomials.
If the coefficient vectors of the images have fewer coordinates than the family
has elements, their linear dependence gives a nonzero polynomial relation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

variable {E : Type*} [Field E]

private theorem relation_of_count {X Y I J : Type*}
    [Fintype X] [Fintype I] [Fintype J] (g : X → MvPolynomial Y E)
    {D b : ℕ} (hg : ∀ i, (g i).totalDegree ≤ D)
    (s : I → X →₀ ℕ) (hinj : Function.Injective s)
    (hdeg : ∀ i, ∑ x, s i x ≤ b) (t : J → Y →₀ ℕ)
    (hcovers : ∀ d : Y →₀ ℕ, d.sum (fun _ n => n) ≤ b * D → ∃ j, t j = d)
    (hcard : Fintype.card J < Fintype.card I) :
    ∃ W : MvPolynomial X E, W ≠ 0 ∧ W.totalDegree ≤ b ∧ aeval g W = 0 := by
  classical
  let image (i : I) : MvPolynomial Y E := ∏ x, g x ^ s i x
  have image_deg (i : I) : (image i).totalDegree ≤ b * D := calc
    _ ≤ ∑ x, (g x ^ s i x).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ x, s i x * D := Finset.sum_le_sum fun x _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg x))
    _ ≤ b * D := by rw [← Finset.sum_mul]; exact Nat.mul_le_mul_right _ (hdeg i)
  let vectors (i : I) (j : J) := (image i).coeff (t j)
  have hdep : ¬ LinearIndependent E vectors := by
    intro h
    exact hcard.not_ge (by simpa only [Module.finrank_pi] using h.fintype_card_le_finrank)
  obtain ⟨a, ha, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let W : MvPolynomial X E := ∑ u, monomial (s u) (a u)
  have nonzero : W ≠ 0 := by
    intro hz
    have h := congrArg (fun p : MvPolynomial X E => p.coeff (s i)) hz
    exact hi (by simpa [W, coeff_sum, coeff_monomial, hinj.eq_iff] using h)
  refine ⟨W, nonzero, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro u _
    refine (totalDegree_monomial_le _ _).trans ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact hdeg u
  · have him : aeval g W = ∑ u, a u • image u := by
      simp only [W, map_sum, aeval_monomial, smul_eq_C_mul, algebraMap_eq]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finsupp.prod_fintype _ _ (by simp)]
    rw [him]
    let p := ∑ u, a u • image u
    change p = 0
    have hp : p.totalDegree ≤ b * D := totalDegree_finsetSum_le fun u _ =>
      (totalDegree_smul_le (a u) (image u)).trans (image_deg u)
    apply MvPolynomial.ext
    intro d
    by_cases hmem : d ∈ p.support
    · obtain ⟨j, rfl⟩ := hcovers d ((le_totalDegree hmem).trans hp)
      simpa [p, vectors, coeff_sum, coeff_smul, Finset.sum_apply] using congrFun ha j
    · simpa using not_ne_iff.mp (mt mem_support_iff.mpr hmem)

private noncomputable def sourceDegree {m b : ℕ} (u : Fin (b + 1) × Simplex m b) :
    Fin (m + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons u.1.val fun i => (u.2.val i).val)

private theorem sourceDegree_injective {m b : ℕ} :
    Function.Injective (sourceDegree (m := m) (b := b)) := by
  intro u v h
  apply Prod.ext
  · exact Fin.ext (DFunLike.congr_fun h 0)
  · apply Subtype.ext
    funext i
    exact Fin.ext (DFunLike.congr_fun h i.succ)

private theorem sum_sourceDegree_le {m b : ℕ} (u : Fin (b + 1) × Simplex m b) :
    ∑ x, sourceDegree u x ≤ 2 * b := by
  rw [Fin.sum_univ_succ, two_mul]
  exact Nat.add_le_add (Nat.le_of_lt_succ u.1.isLt) u.2.property

private noncomputable def targetDegree {m T : ℕ} (v : Simplex m T) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (v.val i).val

private theorem targetDegree_covers {m T : ℕ} (d : Fin m →₀ ℕ)
    (h : d.sum (fun _ n => n) ≤ T) : ∃ v : Simplex m T, targetDegree v = d := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
  have hb (i : Fin m) : d i ≤ T :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans h
  refine ⟨⟨fun i => ⟨d i, Nat.lt_succ_of_le (hb i)⟩, h⟩, ?_⟩
  ext i
  rfl

/-- Any `m + 1` polynomials of degree at most `D` in `m` variables satisfy a
nonzero formal polynomial relation of total degree at most `2 * (2 * (D + 1)) ^ m`. -/
theorem perron_relation {m D : ℕ} (g : Fin (m + 1) → MvPolynomial (Fin m) E)
    (hg : ∀ i, (g i).totalDegree ≤ D) :
    ∃ W : MvPolynomial (Fin (m + 1)) E,
      W ≠ 0 ∧ W.totalDegree ≤ perronSimplexBound m D ∧ aeval g W = 0 :=
  relation_of_count g hg (sourceDegree (b := perronRadius m D)) sourceDegree_injective
    sum_sourceDegree_le targetDegree targetDegree_covers (perron_simplex_card_lt m D)

end RadicalCertificate

end VPVNP
end Computability
end OAI
