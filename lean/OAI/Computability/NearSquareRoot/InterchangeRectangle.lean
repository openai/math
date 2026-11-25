import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Shared label transfers for interchange

The rank part of a query uses selected *actual* rows and columns. This matters
for routing: only these rows and columns have the rectangle incidence bounds.
All the sums below use the same common address at both occurrences of a source.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open scoped BigOperators

variable {K L : Type*} [Field K] [Fintype L]

/-- Skeleton factorization using exactly as many original rows and columns as
the rank. The selected minor is nonsingular, including the empty minor when
the rank is zero. -/
theorem exists_skeleton (A : Matrix L L K) :
    ∃ I J : Fin A.rank → L, Function.Injective I ∧ Function.Injective J ∧
      IsUnit (A.submatrix I J) ∧
      A.submatrix id J * (A.submatrix I J)⁻¹ * A.submatrix I id = A := by
  classical
  have h := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols] at h
  obtain ⟨f, hf, hspan, hind⟩ := h
  choose J hJ using hf
  let C := A.submatrix id J
  have hc : C.col = f := funext hJ
  have hCJ : Function.Injective J := by
    intro i j hij
    exact hind.injective ((hJ i).symm.trans ((congrArg A.col hij).trans (hJ j)))
  have hD (j : L) : ∃ c : Fin A.rank → K, ∑ t, c t • C.col t = A.col j := by
    apply (Submodule.mem_span_range_iff_exists_fun K).mp
    rw [hc, hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose d hd using hD
  let D : Matrix (Fin A.rank) L K := Matrix.of fun i j => d j i
  have hCD : C * D = A := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.col, D, Finset.sum_apply, mul_comm] using
      congrFun (hd j) i
  have hCrank : C.rank = A.rank := by
    rw [C.rank_eq_finrank_span_cols, hc, hspan, ← A.rank_eq_finrank_span_cols]
  have h := Submodule.exists_fun_fin_finrank_span_eq K (Set.range C.row)
  rw [← C.rank_eq_finrank_span_row, hCrank] at h
  obtain ⟨g, hg, _, hgi⟩ := h
  choose I hI using hg
  let M := A.submatrix I J
  have hm : M.row = g := funext hI
  have hu : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp (hm ▸ hgi)
  refine ⟨I, J, ?_, hCJ, hu, ?_⟩
  · intro i j hij
    exact hgi.injective ((hI i).symm.trans ((congrArg C.row hij).trans (hI j)))
  · have hselected : M * D = A.submatrix I id := by
      ext i j
      exact congrFun (congrFun hCD (I i)) j
    change C * M⁻¹ * A.submatrix I id = A
    rw [← hselected, Matrix.mul_assoc, M.nonsing_inv_mul_cancel_left D
      (M.isUnit_iff_isUnit_det.mp hu), hCD]


/-- A directed rectangle sends all its sources to all its destinations. -/
structure Rectangle (L : Type*) where
  sources : Finset L
  destinations : Finset L

variable {B E : Type*} [Fintype B] [AddCommGroup E] [Module K E]
variable [DecidableEq L]

/-- The label matrix is the diagonal plus the sum of the directed rectangles.
For a disjoint partition of the off-diagonal support every entry is zero or one. -/
def rectangleMatrix (r : B → Rectangle L) : Matrix L L K :=
  Matrix.of fun w v => (if w = v then 1 else 0) +
    ∑ b, if w ∈ (r b).destinations ∧ v ∈ (r b).sources then 1 else 0

omit [Fintype L] in
/-- Identify the matrix of an exact disjoint off-diagonal rectangle partition
with the Boolean label matrix, over any characteristic. -/
theorem rectangleMatrix_of_partition (r : B → Rectangle L) (edges : L → L → Prop)
    [DecidableRel edges]
    (cover : ∀ w v, edges w v ↔ ∃ b, w ∈ (r b).destinations ∧ v ∈ (r b).sources)
    (offDiag : ∀ w, ¬ edges w w)
    (disjoint : ∀ w v b c, w ∈ (r b).destinations → v ∈ (r b).sources →
      w ∈ (r c).destinations → v ∈ (r c).sources → b = c) :
    rectangleMatrix (K := K) r = Matrix.of fun w v => if w = v ∨ edges w v then 1 else 0 := by
  classical
  ext w v
  simp only [rectangleMatrix, Matrix.of_apply]
  by_cases h : edges w v
  · obtain ⟨b, hw, hv⟩ := (cover w v).1 h
    have hne : w ≠ v := by rintro rfl; exact offDiag w h
    rw [Fintype.sum_eq_single b (fun c hc => ite_eq_right (fun ⟨hw', hv'⟩ =>
      hc (disjoint w v c b hw' hv' hw hv)))]
    simp [hne, h, hw, hv]
  · have hnone (b : B) : ¬(w ∈ (r b).destinations ∧ v ∈ (r b).sources) :=
      fun hb => h ((cover w v).2 ⟨b, hb⟩)
    simp [hnone, h]

/-- Matrix application to any data module, such as a row of extension-field symbols. -/
def applyRows {I J : Type*} [Fintype J] (M : Matrix I J K) (x : J → E) (i : I) : E :=
  ∑ j, M i j • x j

theorem applyRows_mul {I J H : Type*} [Fintype J] [Fintype H]
    (M : Matrix I J K) (N : Matrix J H K) (x : H → E) :
    applyRows (M * N) x = applyRows M (applyRows N x) := by
  ext1 i
  simp only [applyRows, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- The common-address contribution of the rectangles. Each rectangle's inner
sum is independent of the destination, so one copy suffices before distribution. -/
def rectangleSum (r : B → Rectangle L) (x : L → E) (w : L) : E :=
  ∑ b, if w ∈ (r b).destinations then ∑ v ∈ (r b).sources, x v else 0

omit [Fintype L] in
/-- A selected row or column of the label matrix can be gathered or distributed
using only its incident rectangles. The maps select original source and
destination labels and need not be surjective. -/
theorem selected_applyRows {I J : Type*} [Fintype J]
    (r : B → Rectangle L) (dest : I → L) (src : J → L) (x : J → E) (i : I) :
    applyRows ((rectangleMatrix (K := K) r).submatrix dest src) x i =
      (∑ j, if dest i = src j then x j else 0) +
      ∑ b, if dest i ∈ (r b).destinations then
        ∑ j, if src j ∈ (r b).sources then x j else 0 else 0 := by
  classical
  simp only [applyRows, Matrix.submatrix_apply, rectangleMatrix, Matrix.of_apply,
    add_smul, Finset.sum_add_distrib, Finset.sum_smul, ite_smul, one_smul, zero_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hi : dest i ∈ (r b).destinations <;> simp [hi]

theorem rectangleMatrix_apply (r : B → Rectangle L) (x : L → E) (w : L) :
    applyRows (rectangleMatrix (K := K) r) x w = x w + rectangleSum r x w := by
  simpa [rectangleSum, ← Finset.sum_filter, Finset.filter_mem_eq_inter] using
    selected_applyRows (K := K) r id id x w

/-- The aligned, rank-sized route followed by rectangle subtraction implements
the independent address change on every label. In the interchange construction
the two layouts differ by swapping the query's two fields. All quantifiers
over layouts and payloads are outside the choice of rows and columns. -/
theorem shared_transfer {Addr : Type*} (r : B → Rectangle L) :
    let P := rectangleMatrix (K := K) r
    ∃ I J : Fin P.rank → L, Function.Injective I ∧ Function.Injective J ∧
      IsUnit (P.submatrix I J) ∧
      ∀ (S T : L → Equiv.Perm Addr) (X : L → Addr → E) (w : L) (d : Addr),
        let x := fun v => X v ((S v).symm (T w d))
        let gathered := fun i => x (I i) + rectangleSum r x (I i)
        let mixed := applyRows (P.submatrix I J)⁻¹ gathered
        applyRows (P.submatrix id J) mixed w - rectangleSum r x w =
          X w ((S w).symm (T w d)) := by
  classical
  let P := rectangleMatrix (K := K) r
  obtain ⟨I, J, hI, hJ, hu, h⟩ := exists_skeleton P
  refine ⟨I, J, hI, hJ, hu, ?_⟩
  intro S T X w d
  let x := fun v => X v ((S v).symm (T w d))
  have hg : (fun i => x (I i) + rectangleSum r x (I i)) =
      applyRows (P.submatrix I id) x := by
    funext i
    exact (rectangleMatrix_apply (K := K) r x (I i)).symm
  change applyRows (P.submatrix id J)
      (applyRows (P.submatrix I J)⁻¹ (fun i => x (I i) + rectangleSum r x (I i))) w
        - rectangleSum r x w = x w
  rw [hg, ← applyRows_mul, ← applyRows_mul, h,
    rectangleMatrix_apply (K := K) r x w, add_sub_cancel_right]

end Interchange

end NearSquareRoot
end Computability
end OAI
