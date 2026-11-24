import OAI.Computability.VPVNP.CoordinateQueries
import OAI.Computability.VPVNP.MacaulayRelations
import OAI.Computability.VPVNP.FiniteSlice

/-!
# Coordinates from the augmented Macaulay matrix

Appendix D puts the Macaulay rows first and then the powered monomial rows.
A greedy coordinate query in this order returns a representation of the target.
Discarding the coefficients of the Macaulay rows gives a representation in the
quotient by their span, hence a representation of the original polynomial on
the slice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery

variable {K : Type*} {w n m : ℕ}

/-- Concatenate two lists of rows, retaining their column indexing. -/
def appendRows (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K) :
    Matrix (Fin (w + n)) (Fin m) K := Fin.addCases W M

@[simp] theorem appendRows_left (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (i : Fin w) :
    appendRows W M (i.castAdd n) = W i := Fin.addCases_left ..

@[simp] theorem appendRows_right (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (j : Fin n) :
    appendRows W M (j.natAdd w) = M j := Fin.addCases_right ..

variable [Field K]

/-- A row in the appended block increases the prefix rank exactly when its
class in the quotient increases the span of the preceding appended rows. -/
theorem mem_appendRows_greedy_iff (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (j : Fin n) :
    j.natAdd w ∈ greedyIndices K (appendRows W M).row ↔
      j ∈ greedyIndices K ((Submodule.span K (Set.range W.row)).mkQ ∘ M.row) := by
  let S := Submodule.span K (Set.range W.row)
  have himage : (appendRows W M).row '' Set.Iio (j.natAdd w) =
      Set.range W.row ∪ M.row '' Set.Iio j := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      revert hi
      refine Fin.addCases (fun i _ ↦ ?_) (fun i hi ↦ ?_) i
      · exact Or.inl ⟨i, (appendRows_left W M i).symm⟩
      · refine Or.inr ⟨i, ?_, (appendRows_right W M i).symm⟩
        change w + i.val < w + j.val at hi
        exact Nat.lt_of_add_lt_add_left hi
    · rintro (⟨i, rfl⟩ | ⟨i, hi, rfl⟩)
      · refine ⟨i.castAdd n, ?_, appendRows_left W M i⟩
        exact lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
      · exact ⟨i.natAdd w, Nat.add_lt_add_left hi w, appendRows_right W M i⟩
  rw [mem_greedyIndices, mem_greedyIndices, himage, Submodule.span_union]
  rw [show (appendRows W M).row (j.natAdd w) = M j from appendRows_right W M j]
  change M j ∉ S ⊔ Submodule.span K (M.row '' Set.Iio j) ↔
    S.mkQ (M j) ∉ Submodule.span K ((S.mkQ ∘ M.row) '' Set.Iio j)
  rw [Set.image_comp, ← Submodule.map_span]
  change M j ∉ S ⊔ Submodule.span K (M.row '' Set.Iio j) ↔
    M j ∉ ((Submodule.span K (M.row '' Set.Iio j)).map S.mkQ).comap S.mkQ
  rw [Submodule.comap_map_mkQ]

variable [DecidableEq K]

/-- Query the coefficient assigned to an original row. Only a selected row
contributes a term to the sum over greedy basis indices. -/
def originalRowCoordinate (A : Matrix (Fin n) (Fin m) K) (target : Fin m → K) (j : Fin n) : K :=
  streamSum (rankQuery A) fun k ↦ if greedyRowIndex A k = j then greedyCoordinateQuery A target k else 0

theorem originalRowCoordinate_eq_zero (A : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    {j : Fin n} (hj : j ∉ greedyIndices K A.row) : originalRowCoordinate A target j = 0 := by
  rw [originalRowCoordinate, streamSum_eq]
  apply Finset.sum_eq_zero
  intro k _
  apply ite_eq_right_iff.mpr
  intro he
  exfalso
  apply hj
  rw [← he, greedyRowIndex_eq]
  exact Finset.orderEmbOfFin_mem ..

theorem originalRowCoordinate_reconstruct (A : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    (hspan : target ∈ Submodule.span K (Set.range A.row)) :
    ∑ j, originalRowCoordinate A target j • A j = target := by
  simp only [originalRowCoordinate, streamSum_eq, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  simpa using greedyCoordinateQuery_reconstruct A target hspan

/-- The monomial coefficients, indexed by the second block of the augmented matrix. -/
def quotientCoordinate (W : Matrix (Fin w) (Fin m) K) (M : Matrix (Fin n) (Fin m) K)
    (target : Fin m → K) (j : Fin n) : K :=
  originalRowCoordinate (appendRows W M) target (j.natAdd w)

/-- The difference between the target and the combination of retained monomial
rows belongs to the span of the original Macaulay rows. -/
theorem quotientCoordinate_reconstruct (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    (hspan : target ∈ Submodule.span K (Set.range (appendRows W M).row)) :
    target - ∑ j, quotientCoordinate W M target j • M j ∈ Submodule.span K (Set.range W.row) := by
  have he := originalRowCoordinate_reconstruct (appendRows W M) target hspan
  rw [Fin.sum_univ_add] at he
  simp only [appendRows_left, appendRows_right] at he
  unfold quotientCoordinate
  rw [sub_eq_iff_eq_add.mpr he.symm]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Equality in the quotient by the Macaulay row space after discarding its coordinates. -/
theorem quotientCoordinate_eq_mkQ (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (target : Fin m → K)
    (hspan : target ∈ Submodule.span K (Set.range (appendRows W M).row)) :
    let π := (Submodule.span K (Set.range W.row)).mkQ
    π target = ∑ j, quotientCoordinate W M target j • π (M j) := by
  let S := Submodule.span K (Set.range W.row)
  have h := quotientCoordinate_reconstruct W M target hspan
  have hz : S.mkQ (target - ∑ j, quotientCoordinate W M target j • M j) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr h
  simpa only [map_sub, map_sum, map_smul, sub_eq_zero, S] using hz

omit [DecidableEq K] in
private theorem mem_append_of_difference (W : Matrix (Fin w) (Fin m) K)
    (M : Matrix (Fin n) (Fin m) K) (target : Fin m → K) (c : Fin n → K)
    (hc : target - ∑ j, c j • M j ∈ Submodule.span K (Set.range W.row)) :
    target ∈ Submodule.span K (Set.range (appendRows W M).row) := by
  let T := Submodule.span K (Set.range (appendRows W M).row)
  have hleft : Submodule.span K (Set.range W.row) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.castAdd n, appendRows_left W M i⟩
  have hright : ∑ j, c j • M j ∈ T := T.sum_mem fun j _ ↦
    T.smul_mem _ (Submodule.subset_span ⟨j.natAdd w, appendRows_right W M j⟩)
  simpa using T.add_mem (hleft hc) hright

/-- Reindex the coefficient columns and the Macaulay rows for an indexed
determinant query. The chosen order of the appended list is retained. -/
def indexedQuotientCoordinate {I J : Type*} (W : Matrix I J K) (M : Matrix (Fin n) J K)
    (rows : Fin w ≃ I) (cols : Fin m ≃ J) (target : J → K) : Fin n → K :=
  quotientCoordinate (W.submatrix rows cols) (M.submatrix id cols) (target ∘ cols)

omit [DecidableEq K] in
theorem reindexed_difference_mem_iff {I J : Type*} (W : Matrix I J K) (M : Matrix (Fin n) J K)
    (rows : Fin w ≃ I) (cols : Fin m ≃ J) (target : J → K) (c : Fin n → K) :
    target ∘ cols - ∑ j, c j • (M.submatrix id cols) j ∈
        Submodule.span K (Set.range (W.submatrix rows cols).row) ↔
      target - ∑ j, c j • M j ∈ Submodule.span K (Set.range W.row) := by
  let φ := (LinearEquiv.funCongrLeft K K cols).toLinearMap
  let W' := W.submatrix rows cols
  let M' := M.submatrix id cols
  have hrows : Set.range W'.row = φ '' Set.range W.row := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨W (rows i), ⟨rows i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨rows.symm i, ?_⟩
      funext j
      change W (rows (rows.symm i)) (cols j) = W i (cols j)
      rw [rows.apply_symm_apply]
  have he : φ (target - ∑ j, c j • M j) = target ∘ cols - ∑ j, c j • M' j := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rfl
  rw [← he, hrows]
  exact Submodule.apply_mem_span_image_iff_mem_span (LinearEquiv.funCongrLeft K K cols).injective

theorem indexedQuotientCoordinate_reconstruct {I J : Type*} (W : Matrix I J K)
    (M : Matrix (Fin n) J K) (rows : Fin w ≃ I) (cols : Fin m ≃ J) (target : J → K)
    (hspan : ∃ c : Fin n → K, target - ∑ j, c j • M j ∈ Submodule.span K (Set.range W.row)) :
    target - ∑ j, indexedQuotientCoordinate W M rows cols target j • M j ∈
      Submodule.span K (Set.range W.row) := by
  let W' := W.submatrix rows cols
  let M' := M.submatrix id cols
  have htransfer := reindexed_difference_mem_iff W M rows cols target
  obtain ⟨c, hc⟩ := hspan
  apply (htransfer _).mp
  exact quotientCoordinate_reconstruct W' M' _ (mem_append_of_difference W' M' _ c ((htransfer c).mpr hc))

omit [DecidableEq K] in
theorem mem_greedyIndices_iff_no_prefix_coordinates {V : Type*} [AddCommGroup V] [Module K V]
    (f : Fin n → V) (j : Fin n) :
    j ∈ greedyIndices K f ↔ ¬∃ c : Fin j.val → K, f j = ∑ i, c i • f (Fin.castLE j.isLt.le i) := by
  have hpre : Set.range (f ∘ Fin.castLE j.isLt.le) = f '' Set.Iio j := by
    rw [Set.range_comp, Fin.range_castLE]
    rfl
  rw [mem_greedyIndices, ← hpre, Submodule.mem_span_range_iff_exists_fun K]
  simp only [Function.comp_apply, eq_comm]

end RankQuery

namespace RadicalCertificate

open MvPolynomial RankQuery

variable {K E ι : Type*} [Field K] [Fintype K] [Field E] [Algebra K E] [Fintype ι]
variable {t n : ℕ}

/-- The D.1 row test for representing one polynomial by a linear combination of a list. -/
theorem poweredDifference_relation_iff (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K) (target : MvPolynomial (Fin t) K) (c : Fin n → K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀) (ht : target.totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H) :
    let P := Fintype.card K ^ s
    let L := H + P * R₀
    (∀ x : Fin t → E, (∀ i, aeval x (F i) = 0) →
      aeval x target = ∑ j, c j • aeval x (p j)) ↔
      coefficientRow (L + d) (target ^ P) - ∑ j, c j • coefficientRow (L + d) (p j ^ P) ∈
        Submodule.span K (Set.range (macaulayMatrix F L (L + d)).row) := by
  let polys : Option (Fin n) → MvPolynomial (Fin t) K := Option.elim' target p
  let scalars : Option (Fin n) → K := Option.elim' 1 (fun j ↦ -c j)
  have hdeg : ∀ j, (polys j).totalDegree ≤ R₀ := by
    rintro (_ | j)
    · exact ht
    · exact hp j
  have h := poweredRows_relation_iff F polys scalars hHP hF hdeg bound
  dsimp only at h ⊢
  simpa only [polys, scalars, Fintype.sum_option, Option.elim'_none, Option.elim'_some,
    one_smul, neg_smul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero] using h

/-- The row criterion as an equality in the reduced coordinate algebra. -/
theorem poweredDifference_class_iff (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K) (target : MvPolynomial (Fin t) K) (c : Fin n → K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀) (ht : target.totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H) :
    let V := {x : Fin t → E | ∀ i, aeval x (F i) = 0}
    let π := Ideal.Quotient.mkₐ K (vanishingIdeal K V)
    let P := Fintype.card K ^ s
    let L := H + P * R₀
    π target = ∑ j, c j • π (p j) ↔
      coefficientRow (L + d) (target ^ P) - ∑ j, c j • coefficientRow (L + d) (p j ^ P) ∈
        Submodule.span K (Set.range (macaulayMatrix F L (L + d)).row) := by
  intro V π P L
  refine Iff.trans ?_ (poweredDifference_relation_iff F p target c hHP hF hp ht bound)
  have hpoint (x : V) :
      FiniteSlice.sliceEvaluation V (∑ j, c j • π (p j)) x = ∑ j, c j • aeval x.val (p j) := by
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]
    rfl
  constructor
  · intro he x hx
    exact (congrArg (fun a ↦ FiniteSlice.sliceEvaluation V a ⟨x, hx⟩) he).trans (hpoint ⟨x, hx⟩)
  · intro he
    apply FiniteSlice.sliceEvaluation_injective V
    funext x
    exact (he x.val x.prop).trans (hpoint x).symm

variable [DecidableEq K] {w m L D : ℕ}

/-- Query the coordinates of a polynomial from the Macaulay rows followed by
the powered rows of the supplied list. Both finite indexings of the Macaulay
matrix are explicit, so the query can use the paper's monomial order. -/
noncomputable def macaulayCoordinateQuery (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K) (target : MvPolynomial (Fin t) K) (P : ℕ)
    (rows : Fin w ≃ ι × BoundedMonomial t L) (cols : Fin m ≃ BoundedMonomial t D) : Fin n → K :=
  indexedQuotientCoordinate (macaulayMatrix F L D) (fun j ↦ coefficientRow D (p j ^ P))
    rows cols (coefficientRow D (target ^ P))

/-- The determinant query on the actual Macaulay matrix reconstructs any target
class in the span of the queried polynomials. The degree hypothesis is the
effective weak Nullstellensatz bound used in D.1. -/
theorem macaulayCoordinateQuery_reconstruct (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K) (target : MvPolynomial (Fin t) K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀) (ht : target.totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H)
    (rows : Fin w ≃ ι × BoundedMonomial t (H + Fintype.card K ^ s * R₀))
    (cols : Fin m ≃ BoundedMonomial t (H + Fintype.card K ^ s * R₀ + d)) :
    let V := {x : Fin t → E | ∀ i, aeval x (F i) = 0}
    let π := Ideal.Quotient.mkₐ K (vanishingIdeal K V)
    π target ∈ Submodule.span K (Set.range (fun j ↦ π (p j))) →
      π target = ∑ j, macaulayCoordinateQuery F p target (Fintype.card K ^ s) rows cols j • π (p j) := by
  intro V π hspan
  let P := Fintype.card K ^ s
  let L := H + P * R₀
  let W := macaulayMatrix F L (L + d)
  let M : Matrix (Fin n) (BoundedMonomial t (L + d)) K := fun j ↦ coefficientRow (L + d) (p j ^ P)
  let v := coefficientRow (L + d) (target ^ P)
  have hclass (c : Fin n → K) := poweredDifference_class_iff F p target c hHP hF hp ht bound
  apply (hclass _).mpr
  apply indexedQuotientCoordinate_reconstruct W M rows cols v
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  exact ⟨c, (hclass c).mp hc.symm⟩

omit [DecidableEq K] in
/-- After the Macaulay prefix, exactly the greedy basis indices in the reduced
coordinate algebra are selected, in the given order of the polynomial list. -/
theorem macaulay_greedyIndex_iff (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H)
    (rows : Fin w ≃ ι × BoundedMonomial t (H + Fintype.card K ^ s * R₀))
    (cols : Fin m ≃ BoundedMonomial t (H + Fintype.card K ^ s * R₀ + d)) (j : Fin n) :
    let V := {x : Fin t → E | ∀ i, aeval x (F i) = 0}
    let π := Ideal.Quotient.mkₐ K (vanishingIdeal K V)
    let P := Fintype.card K ^ s
    let L := H + P * R₀
    let W := macaulayMatrix F L (L + d)
    let M : Matrix (Fin n) (BoundedMonomial t (L + d)) K := fun i ↦ coefficientRow (L + d) (p i ^ P)
    j.natAdd w ∈ greedyIndices K (appendRows (W.submatrix rows cols) (M.submatrix id cols)).row ↔
      j ∈ greedyIndices K (fun i ↦ π (p i)) := by
  intro V π P L W M
  rw [mem_appendRows_greedy_iff, mem_greedyIndices_iff_no_prefix_coordinates,
    mem_greedyIndices_iff_no_prefix_coordinates]
  apply not_congr
  apply exists_congr
  intro c
  let inc := Fin.castLE j.isLt.le
  let S := Submodule.span K (Set.range (W.submatrix rows cols).row)
  let diff := M j ∘ cols - ∑ i, c i • (M (inc i) ∘ cols)
  have hdiff : S.mkQ (M j ∘ cols) = ∑ i, c i • S.mkQ (M (inc i) ∘ cols) ↔ diff ∈ S := by
    have hz : S.mkQ diff = 0 ↔ diff ∈ S := Submodule.Quotient.mk_eq_zero _
    simpa only [diff, map_sub, map_sum, map_smul, sub_eq_zero] using hz
  refine hdiff.trans ?_
  apply (reindexed_difference_mem_iff W (M.submatrix inc id) rows cols (M j) c).trans
  exact (poweredDifference_class_iff F (p ∘ inc) (p j) c hHP hF (fun i ↦ hp (inc i)) (hp j) bound).symm

/-- The coordinate query returns zero off the selected polynomial basis in
the reduced algebra, including for repeated or zero polynomial classes. -/
theorem macaulayCoordinateQuery_eq_zero (F : ι → MvPolynomial (Fin t) K)
    (p : Fin n → MvPolynomial (Fin t) K) (target : MvPolynomial (Fin t) K)
    {H s R₀ d : ℕ} (hHP : H ≤ Fintype.card K ^ s) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hp : ∀ j, (p j).totalDegree ≤ R₀)
    (bound : WeakCertificateBound E (Option ι) (t + 1) (max d (R₀ + 1)) H)
    (rows : Fin w ≃ ι × BoundedMonomial t (H + Fintype.card K ^ s * R₀))
    (cols : Fin m ≃ BoundedMonomial t (H + Fintype.card K ^ s * R₀ + d)) (j : Fin n) :
    let V := {x : Fin t → E | ∀ i, aeval x (F i) = 0}
    let π := Ideal.Quotient.mkₐ K (vanishingIdeal K V)
    j ∉ greedyIndices K (fun i ↦ π (p i)) →
      macaulayCoordinateQuery F p target (Fintype.card K ^ s) rows cols j = 0 := by
  intro V π hj
  apply originalRowCoordinate_eq_zero
  exact (macaulay_greedyIndex_iff F p hHP hF hp bound rows cols j).not.mpr hj

end RadicalCertificate

end VPVNP
end Computability
end OAI
