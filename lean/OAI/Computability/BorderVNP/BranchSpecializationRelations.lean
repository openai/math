import OAI.Computability.BorderVNP.Model
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The finite matrix of polynomial relations

In Lemma 9.1 the rows record the coefficients of bounded-degree monomials after
substitution by a polynomial map. A point in the image closure gives a row
expression for its monomial evaluations over the field of definition. Conversely
a row expression after reduction kills every bounded-degree relation, including
relations whose coefficients belong to an extension of the residue field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace BranchSpecialization

open MvPolynomial
open scoped Matrix

/-- Exponent vectors of monomials of total degree at most `D`. -/
def BoundedMonomial (σ : Type*) (D : ℕ) := {m : σ →₀ ℕ // m.degree ≤ D}

noncomputable instance {σ : Type*} [Finite σ] (D : ℕ) : Fintype (BoundedMonomial σ D) :=
  (Finsupp.finite_of_degree_le (σ := σ) D).fintype

/-- The substitution matrix of Lemma 9.1 with every monomial of degree at most `D`
as a column and every parameter monomial of degree at most `d * D` as a row. -/
noncomputable def relationMatrix {ι σ R : Type*} [CommSemiring R]
    (Y : ι → MvPolynomial σ R) (d D : ℕ) :
    Matrix (BoundedMonomial σ (d * D)) (BoundedMonomial ι D) R :=
  fun a b => (b.val.prod fun i e => Y i ^ e).coeff a.val

/-- Monomial evaluations at the proposed point of the image closure. -/
noncomputable def pointRow {ι R : Type*} [CommSemiring R] (c : ι → R) (D : ℕ) :
    BoundedMonomial ι D → R := fun b => b.val.prod fun i e => c i ^ e

/-- The polynomial image as a set of points in affine space. -/
def polynomialImage {ι σ K : Type*} [CommSemiring K] (Y : ι → MvPolynomial σ K) :
    Set (ι → K) := Set.range fun x : σ → K => fun i => eval x (Y i)

/-- Row expressions commute with reduction of coefficients and with field extension. -/
theorem map_rowExpression {m n R S : Type*} [Fintype m] [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {A : Matrix m n R} {w : m → R} {u : n → R}
    (hw : w ᵥ* A = u) : (f ∘ w) ᵥ* A.map f = f ∘ u := by
  funext j
  exact (f.map_vecMul A w j).symm.trans (congrArg f (congrFun hw j))

/-- Substitution followed by coefficient reduction gives the reduced matrix. -/
theorem relationMatrix_map {ι σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (Y : ι → MvPolynomial σ R) (d D : ℕ) :
    relationMatrix (fun i => map f (Y i)) d D = (relationMatrix Y d D).map f := by
  ext a b
  simp only [relationMatrix, Matrix.map_apply, Finsupp.prod]
  rw [← coeff_map, map_prod]
  simp only [map_pow]

/-- Reduction of the evaluation point gives the reduced row of monomial values. -/
theorem pointRow_map {ι R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (c : ι → R) (D : ℕ) :
    pointRow (f ∘ c) D = f ∘ pointRow c D := by
  funext b
  simp [pointRow, Finsupp.prod, map_prod]

/-- The annihilator of the kernel is the row space, written using explicit row weights. -/
theorem rowExpression_iff {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A : Matrix m n K) (u : n → K) :
    (∃ w : m → K, w ᵥ* A = u) ↔ ∀ v : n → K, A *ᵥ v = 0 → u ⬝ᵥ v = 0 := by
  classical
  constructor
  · rintro ⟨w, rfl⟩ v hv
    rw [← Matrix.dotProduct_mulVec, hv, dotProduct_zero]
  · intro h
    let φ : (n → K) →ₗ[K] K := ∑ i, u i • LinearMap.proj i
    have hφ (v : n → K) : φ v = u ⬝ᵥ v := by
      simp [φ, dotProduct, LinearMap.sum_apply]
    have hm : φ ∈ LinearMap.range A.mulVecLin.dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
      exact fun v hv => (hφ v).trans (h v hv)
    obtain ⟨ψ, hψ⟩ := hm
    let w (i : m) := ψ (fun j => if i = j then 1 else 0)
    refine ⟨w, ?_⟩
    funext j
    have he := DFunLike.congr_fun hψ (Pi.single j 1)
    change ψ (A *ᵥ Pi.single j 1) = φ (Pi.single j 1) at he
    rw [Matrix.mulVec_single_one, hφ, dotProduct_single_one] at he
    rw [LinearMap.pi_apply_eq_sum_univ] at he
    simpa only [Matrix.vecMul, dotProduct, w, smul_eq_mul, Matrix.col_apply, mul_comm] using he

private noncomputable def equation {ι K : Type*} [Finite ι] [CommSemiring K] {D : ℕ}
    (v : BoundedMonomial ι D → K) : MvPolynomial ι K :=
  ∑ b, monomial b.val (v b)

private theorem equation_eval {ι K : Type*} [Finite ι] [CommSemiring K] {D : ℕ}
    (c : ι → K) (v : BoundedMonomial ι D → K) :
    eval c (equation v) = pointRow c D ⬝ᵥ v := by
  simp only [equation, map_sum, eval_monomial, pointRow, dotProduct, mul_comm]

private theorem equation_aeval {ι σ K : Type*} [Finite ι] [CommSemiring K] {D : ℕ}
    (Y : ι → MvPolynomial σ K) (v : BoundedMonomial ι D → K) :
    aeval Y (equation v) = ∑ b, v b • (b.val.prod fun i e => Y i ^ e) := by
  simp only [equation, map_sum, aeval_monomial, smul_eq_C_mul, algebraMap_eq]

private theorem equation_coeff {ι σ K : Type*} [Finite ι] [CommSemiring K] (d D : ℕ)
    (Y : ι → MvPolynomial σ K) (v : BoundedMonomial ι D → K) (a : BoundedMonomial σ (d * D)) :
    (aeval Y (equation v)).coeff a.val = (relationMatrix Y d D *ᵥ v) a := by
  simp only [equation_aeval, coeff_sum, coeff_smul, smul_eq_mul, relationMatrix, Matrix.mulVec,
    dotProduct, mul_comm]

private theorem equation_aeval_degree {ι σ K : Type*} [Finite ι] [CommSemiring K] {d D : ℕ}
    (Y : ι → MvPolynomial σ K) (hY : ∀ i, (Y i).totalDegree ≤ d) (v : BoundedMonomial ι D → K) :
    (aeval Y (equation v)).totalDegree ≤ d * D := by
  rw [equation_aeval]
  apply totalDegree_finsetSum_le
  intro b _
  apply (totalDegree_smul_le _ _).trans
  calc
    _ ≤ ∑ i ∈ b.val.support, (Y i ^ b.val i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ b.val.support, b.val i * d := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hY i))
    _ ≤ d * D := by
      rw [← Finset.sum_mul, Nat.mul_comm d D]
      exact Nat.mul_le_mul_right _ b.property

private theorem substitution_eq_zero_iff {ι σ K : Type*} [Finite ι] [CommSemiring K] {d D : ℕ}
    (Y : ι → MvPolynomial σ K) (hY : ∀ i, (Y i).totalDegree ≤ d) (v : BoundedMonomial ι D → K) :
    aeval Y (equation v) = 0 ↔ relationMatrix Y d D *ᵥ v = 0 := by
  constructor
  · intro he
    funext a
    rw [← equation_coeff, he]
    rfl
  · intro hm
    apply MvPolynomial.ext
    intro a
    by_cases h : a ∈ (aeval Y (equation v)).support
    · have ha := (le_totalDegree h).trans (equation_aeval_degree Y hY v)
      exact (equation_coeff d D Y v ⟨a, ha⟩).trans (congrFun hm ⟨a, ha⟩)
    · exact notMem_support_iff.mp h

private theorem equation_of_coeff {ι K : Type*} [Finite ι] [CommSemiring K] {D : ℕ}
    (q : MvPolynomial ι K) (hq : q.totalDegree ≤ D) :
    equation (fun b : BoundedMonomial ι D => q.coeff b.val) = q := by
  classical
  apply MvPolynomial.ext
  intro a
  rw [equation, coeff_sum]
  by_cases h : a.degree ≤ D
  · let b : BoundedMonomial ι D := ⟨a, h⟩
    have he (i : BoundedMonomial ι D) : i.val = a ↔ i = b :=
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [coeff_monomial, he, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  · have he (i : BoundedMonomial ι D) : i.val ≠ a := fun hi => h (hi ▸ i.property)
    simp only [coeff_monomial, he, ite_false, Finset.sum_const_zero]
    exact (notMem_support_iff.mp (fun ha => h ((le_totalDegree ha).trans hq))).symm

private theorem eval_substitute {ι σ K : Type*} [CommSemiring K]
    (Y : ι → MvPolynomial σ K) (q : MvPolynomial ι K) (x : σ → K) :
    eval x (aeval Y q) = eval (fun i => eval x (Y i)) q := by
  change eval x (eval₂ C Y q) = _
  rw [eval_eval₂]
  have he : (eval x).comp C = RingHom.id K := by ext; simp
  rw [he, eval₂_id]

/-- Over an infinite field, equations on the image are exactly the kernel of
formal polynomial substitution. -/
theorem vanishes_on_polynomialImage_iff {ι σ K : Type*} [Field K] [Infinite K]
    (Y : ι → MvPolynomial σ K) (q : MvPolynomial ι K) :
    (∀ y ∈ polynomialImage Y, eval y q = 0) ↔ aeval Y q = 0 := by
  constructor
  · intro hv
    apply MvPolynomial.funext
    intro x
    rw [eval_substitute, hv _ ⟨x, rfl⟩, map_zero]
  · rintro hv _ ⟨x, rfl⟩
    rw [← eval_substitute, hv, map_zero]

/-- Relabeling the parameters of a polynomial map leaves its image fixed. -/
theorem polynomialImage_rename {ι σ τ K : Type*} [CommSemiring K]
    (e : σ ≃ τ) (Y : ι → MvPolynomial σ K) :
    polynomialImage (fun i => rename e (Y i)) = polynomialImage Y := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x ∘ e, funext fun i => (eval_rename e x (Y i)).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨x ∘ e.symm, funext fun i => ?_⟩
    change eval (x ∘ e.symm) (rename e (Y i)) = eval x (Y i)
    rw [eval_rename, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- An actual affine image-closure point satisfies the row criterion at every degree cutoff. -/
theorem rowExpression_of_mem_imageClosure {ι σ K : Type*} [Finite ι] [Finite σ] [Field K]
    {d : ℕ} (D : ℕ) (Y : ι → MvPolynomial σ K) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (c : ι → K) (hc : c ∈ imageClosure (polynomialImage Y)) :
    ∃ w, w ᵥ* relationMatrix Y d D = pointRow c D := by
  apply (rowExpression_iff _ _).2
  intro v hv
  rw [← equation_eval]
  apply hc
  rintro _ ⟨x, rfl⟩
  rw [← eval_substitute, (substitution_eq_zero_iff Y hY v).2 hv, map_zero]

/-- Over an infinite field every bounded-degree equation vanishing on the polynomial
image vanishes at a point whose monomial values have a row expression. -/
theorem vanishes_of_rowExpression {ι σ K : Type*} [Finite ι] [Finite σ] [Field K] [Infinite K]
    {d D : ℕ} (Y : ι → MvPolynomial σ K) (c : ι → K)
    (hr : ∃ w, w ᵥ* relationMatrix Y d D = pointRow c D)
    (q : MvPolynomial ι K) (hq : q.totalDegree ≤ D)
    (hvan : ∀ y ∈ polynomialImage Y, eval y q = 0) : eval c q = 0 := by
  let v (b : BoundedMonomial ι D) := q.coeff b.val
  have he : equation v = q := equation_of_coeff q hq
  have hzero := (vanishes_on_polynomialImage_iff Y q).1 hvan
  rw [← he, equation_eval]
  apply (rowExpression_iff _ _).1 hr
  funext a
  rw [← equation_coeff, he, hzero]
  rfl

/-- The row expression can be chosen in the field of definition even when the
image-closure hypothesis is given over its algebraic closure or another field extension. -/
theorem rowExpression_of_mem_imageClosure_extension {ι σ K E : Type*}
    [Finite ι] [Finite σ] [Field K] [Field E] (f : K →+* E) {d : ℕ} (D : ℕ)
    (Y : ι → MvPolynomial σ K) (hY : ∀ i, (Y i).totalDegree ≤ d) (c : ι → K)
    (hc : f ∘ c ∈ imageClosure (polynomialImage (fun i => map f (Y i)))) :
    ∃ w, w ᵥ* relationMatrix Y d D = pointRow c D := by
  have hg (i : ι) : (map f (Y i)).totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset f (Y i))).trans (hY i)
  have he := rowExpression_of_mem_imageClosure D _ hg _ hc
  rw [relationMatrix_map, pointRow_map] at he
  apply (rowExpression_iff _ _).2
  intro v hv
  have hm : (relationMatrix Y d D).map f *ᵥ (f ∘ v) = 0 := by
    funext a
    rw [← f.map_mulVec, hv]
    exact f.map_zero
  apply f.injective
  rw [f.map_dotProduct, f.map_zero]
  exact (rowExpression_iff _ _).1 he _ hm

/-- A residue-field row expression implies vanishing of every bounded-degree
image equation over any infinite extension, including the algebraic closure. -/
theorem vanishes_of_rowExpression_extension {ι σ K E : Type*}
    [Finite ι] [Finite σ] [Field K] [Field E] [Infinite E] (f : K →+* E) {d D : ℕ}
    (Y : ι → MvPolynomial σ K) (c : ι → K)
    (hr : ∃ w, w ᵥ* relationMatrix Y d D = pointRow c D)
    (q : MvPolynomial ι E) (hq : q.totalDegree ≤ D)
    (hvan : ∀ y ∈ polynomialImage (fun i => map f (Y i)), eval y q = 0) :
    eval (f ∘ c) q = 0 := by
  obtain ⟨w, hw⟩ := hr
  apply vanishes_of_rowExpression (d := d) (D := D) _ _ _ q hq hvan
  rw [relationMatrix_map, pointRow_map]
  exact ⟨f ∘ w, map_rowExpression f hw⟩

end BranchSpecialization

end BorderVNP
end Computability
end OAI
