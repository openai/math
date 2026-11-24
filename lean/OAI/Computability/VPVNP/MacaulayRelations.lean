import OAI.Computability.VPVNP.MacaulayRows
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear relations in the reduced slice algebra

Appendix D.1 descends a bounded coefficient row test to the field of definition.
A power of the cardinality of this finite field acts linearly on polynomials.
Thus a relation among polynomial values on the slice becomes a relation among
the powered coefficient rows modulo the Macaulay row space.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- Membership of a row over the base field descends through any field extension.
Apply a base-linear retraction of the scalar inclusion to the coefficient equations. -/
theorem rowSpan_descent {I J : Type*} [Fintype I] (M : Matrix I J K) (v : J → K)
    (hv : (fun j ↦ algebraMap K E (v j)) ∈
      Submodule.span E (Set.range (M.map (algebraMap K E)).row)) :
    v ∈ Submodule.span K (Set.range M.row) := by
  let φ := Algebra.linearMap K E
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K E).injective)
  have hfix (k : K) : ψ (algebraMap K E k) = k := DFunLike.congr_fun hψ k
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hv
  refine (Submodule.mem_span_range_iff_exists_fun K).mpr ⟨fun i ↦ ψ (c i), ?_⟩
  ext j
  have hj : ∑ i, (M i j) • c i = algebraMap K E (v j) := by
    simpa [Algebra.smul_def, mul_comm, Matrix.row, Matrix.map_apply,
      Finset.sum_apply] using congrFun hc j
  simpa [Finset.sum_apply, mul_comm, Matrix.row, hfix] using congrArg ψ hj

variable {t : ℕ} {ι : Type*} [Fintype ι]

/-- The bounded Rabinowitsch certificate may have coefficients in an extension field,
even though the matrix and the tested row are over the base field. -/
theorem coefficientRow_pow_mem_of_extension (F : ι → MvPolynomial (Fin t) K)
    {f : MvPolynomial (Fin t) K} (A : ι → MvPolynomial (Fin (t + 1)) E)
    (B : MvPolynomial (Fin (t + 1)) E) {H P R₀ d : ℕ} (hHP : H ≤ P) (hP : P ≠ 0)
    (hA : ∀ i, (A i).totalDegree ≤ H) (hf : f.totalDegree ≤ R₀)
    (hcert : let φ := algebraMap K E
      (∑ i, A i * rename Fin.succ (map φ (F i))) + B * (1 - X 0 * rename Fin.succ (map φ f)) = 1) :
    coefficientRow (H + P * R₀ + d) (f ^ P) ∈ Submodule.span K
      (Set.range (macaulayMatrix F (H + P * R₀) (H + P * R₀ + d)).row) := by
  let φ := algebraMap K E
  have hf' : (map φ f).totalDegree ≤ R₀ := by
    simpa only [totalDegree, support_map_of_injective f φ.injective] using hf
  have he := coefficientRow_pow_mem (fun i ↦ map φ (F i)) A B hHP hP hA hf' hcert (d := d)
  apply rowSpan_descent (E := E)
  have hm (L D : ℕ) : macaulayMatrix (fun i ↦ map φ (F i)) L D = (macaulayMatrix F L D).map φ := by
    ext ⟨i, a⟩ j
    change (monomial a.val 1 * map φ (F i)).coeff j.val = φ ((monomial a.val 1 * F i).coeff j.val)
    rw [← coeff_map, map_mul, map_monomial, φ.map_one]
  rw [hm] at he
  convert he using 1
  ext j
  change φ ((f ^ P).coeff j.val) = ((map φ f) ^ P).coeff j.val
  rw [← map_pow, coeff_map]

/-- A uniform weak Nullstellensatz certificate bound for systems of degree at most
`D` in `n` variables. The extra equation in the Rabinowitsch system has index `none`. -/
def WeakCertificateBound (E I : Type*) [Field E] [Fintype I] (n D H : ℕ) : Prop :=
  ∀ G : I → MvPolynomial (Fin n) E, (∀ i, (G i).totalDegree ≤ D) →
    (¬∃ x : Fin n → E, ∀ i, eval x (G i) = 0) →
    ∃ A : I → MvPolynomial (Fin n) E, (∀ i, (A i).totalDegree ≤ H) ∧ ∑ i, A i * G i = 1

/-- The two directions of the D.1 row-space criterion. The forward direction takes
the uniform degree bound from the effective weak Nullstellensatz as a hypothesis. -/
theorem row_test_of_weakCertificateBound (F : ι → MvPolynomial (Fin t) K)
    (f : MvPolynomial (Fin t) K) {H P R₀ d : ℕ} (hHP : H ≤ P) (hP : P ≠ 0)
    (hF : ∀ i, (F i).totalDegree ≤ d) (hf : f.totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H) :
    (∀ x : Fin t → E, (∀ i, aeval x (F i) = 0) → aeval x f = 0) ↔
      coefficientRow (H + P * R₀ + d) (f ^ P) ∈ Submodule.span K
        (Set.range (macaulayMatrix F (H + P * R₀) (H + P * R₀ + d)).row) := by
  constructor
  · intro hvan
    let φ := algebraMap K E
    let lift (p : MvPolynomial (Fin t) K) := rename Fin.succ (map φ p)
    have hlift (p : MvPolynomial (Fin t) K) : (lift p).totalDegree ≤ p.totalDegree := by
      simpa only [totalDegree, support_map_of_injective p φ.injective] using
        totalDegree_rename_le Fin.succ (map φ p)
    let G : Option ι → MvPolynomial (Fin (t + 1)) E
      | some i => lift (F i)
      | none => 1 - X 0 * lift f
    have hdeg (i : Option ι) : (G i).totalDegree ≤ max d (R₀ + 1) := by
      cases i with
      | some i => exact ((hlift _).trans (hF i)).trans (le_max_left _ _)
      | none =>
        apply le_trans _ (le_max_right _ _)
        apply (mem_restrictTotalDegree ..).mp
        apply Submodule.sub_mem
        · exact (mem_restrictTotalDegree ..).mpr (by simp)
        · apply (mem_restrictTotalDegree ..).mpr
          apply (totalDegree_mul _ _).trans
          rw [totalDegree_X, add_comm]
          exact Nat.add_le_add_right ((hlift _).trans hf) _
    have hno : ¬∃ z : Fin (t + 1) → E, ∀ i, eval z (G i) = 0 := by
      rintro ⟨z, hz⟩
      have he (p : MvPolynomial (Fin t) K) : eval z (lift p) = aeval (z ∘ Fin.succ) p := by
        simp only [lift, eval_rename, eval_map, aeval_def, φ]
      have hzero := hvan (z ∘ Fin.succ) (fun i ↦ (he _).symm.trans (hz (some i)))
      have hbad := hz none
      change eval z (1 - X 0 * lift f) = 0 at hbad
      simp [map_sub, map_mul, he, hzero] at hbad
    obtain ⟨A, hA, ha⟩ := bound G hdeg hno
    apply coefficientRow_pow_mem_of_extension F (fun i ↦ A (some i)) (A none)
      hHP hP (fun i ↦ hA (some i)) hf
    simpa only [Fintype.sum_option, G, lift, add_comm] using ha
  · intro hrow x hx
    have hdeg := (totalDegree_pow f P).trans (Nat.mul_le_mul_left _ hf)
    have he := aeval_eq_zero_of_row_mem F hF (f ^ P) (by omega) hrow x hx
    rw [map_pow] at he
    exact (pow_eq_zero_iff hP).mp he

/-- A power of the field cardinality distributes over linear combinations and fixes
their coefficients. -/
theorem linearCombination_pow_card [Fintype K] (s : ℕ) (c : ι → K)
    (p : ι → MvPolynomial (Fin t) K) :
    (∑ i, c i • p i) ^ (Fintype.card K ^ s) = ∑ i, c i • (p i ^ (Fintype.card K ^ s)) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, pow_mul, ih]
    let φ := FiniteField.frobeniusAlgHom K (MvPolynomial (Fin t) K)
    change φ (∑ i, c i • _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul]
    exact congrArg (c i • ·) (pow_mul (p i) (Fintype.card K ^ s) (Fintype.card K)).symm

/-- Coefficient rows commute with the base-linear Frobenius relation. -/
theorem poweredRows_sum [Fintype K] (s D : ℕ) (c : ι → K)
    (p : ι → MvPolynomial (Fin t) K) :
    coefficientRow D ((∑ i, c i • p i) ^ (Fintype.card K ^ s)) =
      ∑ i, c i • coefficientRow D (p i ^ (Fintype.card K ^ s)) := by
  simp [linearCombination_pow_card, map_sum]

/-- The value relation for a list of queried polynomials is exactly the corresponding
linear relation on their powered rows modulo the Macaulay row space. In particular
this applies to the monomial lists used in the prefix-rank and coordinate tests. -/
theorem poweredRows_relation_iff [Fintype K] {J : Type*} [Fintype J]
    (F : ι → MvPolynomial (Fin t) K) (p : J → MvPolynomial (Fin t) K) (c : J → K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H) :
    let P := Fintype.card K ^ s
    let L := H + P * R₀
    (∀ x : Fin t → E, (∀ i, aeval x (F i) = 0) → ∑ j, c j • aeval x (p j) = 0) ↔
      ∑ j, c j • coefficientRow (L + d) (p j ^ P) ∈ Submodule.span K
        (Set.range (macaulayMatrix F L (L + d)).row) := by
  dsimp only
  have hdeg : (∑ j, c j • p j).totalDegree ≤ R₀ := totalDegree_finsetSum_le
    fun j _ ↦ (totalDegree_smul_le _ _).trans (hp j)
  simpa only [map_sum, map_smul, poweredRows_sum] using
    row_test_of_weakCertificateBound F (∑ j, c j • p j) hHP
      (pow_ne_zero _ Fintype.card_pos.ne') hF hdeg bound

end RadicalCertificate

end VPVNP
end Computability
end OAI
