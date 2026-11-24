import OAI.Computability.VPVNP.LabelEvaluatorIndexedPins
import OAI.Computability.VPVNP.MacaulaySliceBasis

/-!
# The graded monomial basis of the label evaluator

The dense ordinals returned by the prefix-rank algorithm are identified with
the retained indices of a slice presentation. Multiplication and Frobenius
entries in this presentation are exactly the scalars returned by the indexed
query. The distinguished unit is dense ordinal zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.QueryData

open MvPolynomial FiniteSlice RankQuery

variable {K E : Type*} [Field K] [Fintype K] [DecidableEq K] [Field E] [Algebra K E]
    {t k : ℕ}

/-- A slice presentation whose listing, dense basis ordinals and field-valued
queries use the same enumeration of monomials. -/
structure Canonical (S : QueryData t k K) (I : Ideal (MvPolynomial (Fin t) K)) where
  /-- Monomial presentation of the finite-slice coordinate algebra identified with the bounded
  rank-query data. -/
  presentation : SliceEvaluator.Presentation K I S.pointBound (E := E)
  size_eq : presentation.lastIndex + 1 = size t S.pointBound
  listing_eq (j : Fin (presentation.lastIndex + 1)) : presentation.listing j =
    Ideal.Quotient.mkₐ K (vanishingIdeal K (zeroLocus E I))
      (monomialAt t S.pointBound (j.cast size_eq))
  /-- Equivalence from dense basis ordinals to the greedy pivot indices in the canonical
  monomial listing. -/
  ordinal : Fin S.dimension ≃ greedyIndices K presentation.listing
  ordinal_val (j : Fin S.dimension) : (ordinal j).val.val = (S.basisIndex j).val
  unit_ordinal : (ordinal.symm presentation.unitIndex).val = 0
  entry_eq (op : Operation t) (i j : Fin S.dimension) :
    S.matrixEntry op i j = presentation.basis.repr
      (op.apply S.fieldOrder (coordinateLabel (zeroLocus E I)) (presentation.basis (ordinal j))) (ordinal i)

private noncomputable def gradedListing (V : Set (Fin t → E)) (N : ℕ) (j : Fin (size t N)) :
    CoordinateAlgebra K V :=
  Ideal.Quotient.mkₐ K (vanishingIdeal K V) (monomialAt t N j)

private def reindexRetained {A : Type*} [AddCommGroup A] [Module K A]
    {n m : ℕ} (h : m = n) (v : Fin n → A) :
    greedyIndices K v ≃ greedyIndices K (fun j : Fin m => v (j.cast h)) := by
  subst m
  exact Equiv.refl _

omit [Fintype K] [DecidableEq K] in
private theorem reindexRetained_val {A : Type*} [AddCommGroup A] [Module K A]
    {n m : ℕ} (h : m = n) (v : Fin n → A) (j : greedyIndices K v) :
    ((reindexRetained h v) j).val.val = j.val.val := by subst m; rfl

/-- Build the canonical presentation from the very equations used to query
the matrix, allowing any equal presentation of their affine ideal. -/
theorem exists_canonical [IsAlgClosed E] (S : QueryData t k K)
    (F : Fin k → MvPolynomial (Fin t) K) (h : S.Presents F)
    (I : Ideal (MvPolynomial (Fin t) K)) (hI : I = Ideal.span (Set.range F))
    (hn : (zeroLocus E I).Nonempty) (hfin : (zeroLocus E I).Finite)
    (hc : (zeroLocus E I).ncard ≤ S.pointBound) : Nonempty (Canonical (E := E) S I) := by
  classical
  let V := zeroLocus E I
  let N := S.pointBound
  let v := gradedListing (K := K) V N
  let z : Fin (size t N) := ⟨0, size_pos t N⟩
  have hv : V = points F E := by ext x; simp [V, hI, points, zeroLocus_span]
  have data : Set.range v = MonomialBasis.monomials (coordinateLabel V) N ∧ v z = 1 ∧
      Set.range S.basisIndex = (greedyIndices K v : Set _) ∧
      ∃ b : Module.Basis (Fin S.dimension) K (CoordinateAlgebra K V),
        (∀ i, b i = v (S.basisIndex i)) ∧ (∃ u : Fin S.dimension, u.val = 0 ∧ b u = 1) ∧
        ∀ op i j, S.matrixEntry op i j =
          b.repr (op.apply S.fieldOrder (coordinateLabel V) (b j)) i := by
    have hn' : V.Nonempty := hn
    have hf' : V.Finite := hfin
    have hc' : V.ncard ≤ N := hc
    dsimp only [v]
    rw [hv] at hn' hf' hc' ⊢
    obtain ⟨b, hb, hu, _, hm⟩ := S.finite_slice_coordinate_queries F h hn' hf' hc'
    exact ⟨S.listing_range F, S.listing_first F, Set.ext (S.basisIndex_mem_iff F h),
      b, hb, hu, hm⟩
  obtain ⟨hrange, hz, hindices, b, hb, ⟨u, hu, hbu⟩, hm⟩ := data
  have : Nonempty V := hn.to_subtype
  have : Nontrivial (CoordinateAlgebra K V) := coordinateAlgebra_nontrivial V
  have hz' : z ∈ greedyIndices K v := by
    have hempty : Set.Iio z = ∅ := by ext i; simp [z, Fin.le_def]
    rw [mem_greedyIndices, hempty, hz]
    simp
  have hzrange : z ∈ Set.range S.basisIndex := hindices.symm ▸ hz'
  obtain ⟨j, hj⟩ := hzrange
  have hj' : b j = 1 := (hb j).trans (hj ▸ hz)
  have hunit : S.basisIndex u = z := b.injective (hbu.trans hj'.symm) ▸ hj
  let n := size t N - 1
  have hsz : n + 1 = size t N := by dsimp [n]; have := size_pos t N; omega
  let listing (i : Fin (n+1)) := v (i.cast hsz)
  let raw := (Equiv.ofInjective S.basisIndex (suffixBasisIndex_injective S.equations S.monomials)).trans
    (Set.equivOfEq hindices)
  let ord := raw.trans (reindexRetained hsz v)
  have hord (i) : (ord i).val.val = (S.basisIndex i).val :=
    reindexRetained_val hsz v (raw i)
  let basis := b.reindex ord
  have hlist (i : greedyIndices K listing) : basis i = listing i.val := by
    obtain ⟨j, rfl⟩ := ord.surjective i
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hb]
    exact congrArg v (Fin.ext (hord j).symm)
  have hlistRange : Set.range listing = Set.range v :=
    (finCongr hsz).surjective.range_comp v
  let P : SliceEvaluator.Presentation K I N (E := E) :=
    ⟨n, listing, hlistRange.trans hrange, hz, basis, hlist, ord u, Fin.ext ((hord u).trans (congrArg Fin.val hunit))⟩
  refine ⟨⟨P, hsz, fun _ => rfl, ord, hord, ?_, ?_⟩⟩
  · change (ord.symm (ord u)).val = 0
    rwa [Equiv.symm_apply_apply]
  · intro op i j
    change _ = (b.reindex ord).repr (op.apply _ _ ((b.reindex ord) (ord j))) (ord i)
    simp only [Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply]
    exact hm op i j

end RadicalCertificate.MonomialIndex.QueryData

namespace RadicalCertificate.MonomialIndex.QueryData

open MvPolynomial FiniteSlice

variable {K E : Type*} [Field K] [Fintype K] [DecidableEq K] [Field E] [Algebra K E]
    {t k : ℕ} {S : QueryData t k K} {I : Ideal (MvPolynomial (Fin t) K)}

/-- The canonical presentation's basis, indexed by the dense machine ordinals. -/
noncomputable def Canonical.denseBasis (D : Canonical (E := E) S I) :
    Module.Basis (Fin S.dimension) K (CoordinateAlgebra K (zeroLocus E I)) :=
  D.presentation.basis.reindex D.ordinal.symm

omit [Fintype K] in
/-- Ordinal `i` denotes exactly the basis monomial returned by the numeric prefix ranks. -/
theorem Canonical.denseBasis_apply (D : Canonical (E := E) S I) (i : Fin S.dimension) :
    D.denseBasis i = Ideal.Quotient.mkₐ K (vanishingIdeal K (zeroLocus E I))
      (monomialAt t S.pointBound (S.basisIndex i)) := by
  rw [denseBasis, Module.Basis.reindex_apply, Equiv.symm_symm, D.presentation.basis_apply, D.listing_eq]
  exact congrArg (fun j => Ideal.Quotient.mkₐ K _ (monomialAt t S.pointBound j)) (Fin.ext (D.ordinal_val i))

omit [Fintype K] in
/-- The physical query stores the coefficient at the destination ordinal. -/
theorem Canonical.matrixEntry_dense (D : Canonical (E := E) S I) (op : Operation t)
    (dest src : Fin S.dimension) :
    S.matrixEntry op dest src = D.denseBasis.repr
      (op.apply S.fieldOrder (coordinateLabel (zeroLocus E I)) (D.denseBasis src)) dest := by
  simpa only [denseBasis, Module.Basis.reindex_apply, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
    using D.entry_eq op dest src

omit [Fintype K] in
/-- The path matrix is transposed relative to the coefficient array of label multiplication. -/
theorem Canonical.label_transition (D : Canonical (E := E) S I) (j : Fin t)
    (src dest : Fin S.dimension) :
    ((LinearMap.toMatrixAlgEquiv D.denseBasis)
      (LinearMap.mulLeft K (coordinateLabel (zeroLocus E I) j))).transpose src dest =
      S.matrixEntry (.label j) dest src := by
  rw [D.matrixEntry_dense, Matrix.transpose_apply, LinearMap.toMatrixAlgEquiv_apply]
  rfl

/-- The Frobenius path matrix has the same destination/source convention. -/
theorem Canonical.frobenius_transition (D : Canonical (E := E) S I) (hQ : S.fieldOrder = Fintype.card K)
    (src dest : Fin S.dimension) :
    ((LinearMap.toMatrixAlgEquiv D.denseBasis)
      (FiniteField.frobeniusAlgHom K _).toLinearMap).transpose src dest =
      S.matrixEntry .frobenius dest src := by
  rw [D.matrixEntry_dense, Matrix.transpose_apply, LinearMap.toMatrixAlgEquiv_apply, hQ]
  rfl

omit [Fintype K] in
/-- The dense unit ordinal labels the constant monomial. -/
theorem Canonical.denseBasis_unit (D : Canonical (E := E) S I) :
    D.denseBasis (D.ordinal.symm D.presentation.unitIndex) = 1 := by
  rw [denseBasis, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    D.presentation.basis_apply, D.presentation.unitIndex_val, D.presentation.first_eq_one]

/-- The output functional first reads the dense unit ordinal and then the
prime-field coordinate of that coefficient. -/
theorem Canonical.functional_apply {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K]
    (D : Canonical (E := E) S I) (x : CoordinateAlgebra K (zeroLocus E I)) :
    D.presentation.functional (p := p) x = SliceEvaluator.primeCoordinate p K
      (D.denseBasis.repr x (D.ordinal.symm D.presentation.unitIndex)) := by
  simp only [denseBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end RadicalCertificate.MonomialIndex.QueryData

namespace LabelEvaluator

open MvPolynomial RadicalCertificate RadicalCertificate.MonomialIndex

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used to identify the canonical rank-query
presentation. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Decidable equality on the finite ground field used to select canonical pivots. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _
/-- Algebra structure on the ambient field induced by the ground-field embedding for the
canonical presentation. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

variable {p : Nat.Primes} {t d m : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin t) ℤ}

/-- Select the presentation for this exact input reader, prime and advised slice. -/
noncomputable def Model.canonicalPresentation (M : Model p d F) (r : Fin m ≃ ι)
    (read : Fin m → (Fin t → ℕ) → ℤ) (hd : 3 ≤ d) (hdeg : ∀ i, (F i).totalDegree ≤ d)
    (hread : ∀ i a, read i a = (F (r i)).coeff (exponentVector a)) :
    (M.queryData read).Canonical (E := Ambient p) (sliceIdeal p d F M.pins M.values) :=
  Classical.choice ((M.queryData read).exists_canonical (M.indexedEquations r)
    (M.queryData_presents r read hd hdeg hread) _ (M.span_indexedEquations r).symm
    M.nonempty M.finite M.pointCount_le)

/-- Use the verified ordinal basis in the algebraic label evaluator at every
input exponent vector and every bit width. -/
noncomputable def Model.withCanonicalPresentation (M : Model p d F) {read : Fin m → (Fin t → ℕ) → ℤ}
    (D : (M.queryData read).Canonical (E := Ambient p) (sliceIdeal p d F M.pins M.values)) : Model p d F :=
  { M with
    presentation := D.presentation
    listing_length_le := by rw [D.size_eq, size_eq_card]; exact card_boundedMonomial_le .. }

/-- For the rebuilt model the actual physical ordinal in the first coordinate
of the functional has value zero. -/
theorem Model.canonical_functional (M : Model p d F) {read : Fin m → (Fin t → ℕ) → ℤ}
    (D : (M.queryData read).Canonical (E := Ambient p) (sliceIdeal p d F M.pins M.values)) :
    ∃ u : Fin (M.queryData read).dimension, u.val = 0 ∧
      ∀ x : M.algebra, (M.withCanonicalPresentation D).functional x =
        SliceEvaluator.primeCoordinate p.val (Ground p t d) (D.denseBasis.repr x u) :=
  ⟨D.ordinal.symm D.presentation.unitIndex, D.unit_ordinal, D.functional_apply⟩

/-- Counting matrix-index paths on the actual dense ordinals recovers the
functional of the canonical model modulo the advised prime. -/
theorem Model.canonical_pathCount_mod (M : Model p d F) {read : Fin m → (Fin t → ℕ) → ℤ}
    (D : (M.queryData read).Canonical (E := Ambient p) (sliceIdeal p d F M.pins M.values))
    (width : ℕ) (a : Fin t → ℕ) (ha : ∀ i, a i < 2 ^ width) :
    let u := D.ordinal.symm D.presentation.unitIndex
    (Fintype.card (Evaluator.AcceptingBranches (SliceEvaluator.primeCoordinate p.val (Ground p t d))
      (Evaluator.transitionMatrices D.denseBasis (Evaluator.digitProgram (Ground p t d) M.labels width a))
      u u) : ZMod p.val) = (M.withCanonicalPresentation D).functional (∏ i, M.labels i ^ a i) := by
  intro u
  rw [Evaluator.finiteAlgebra_pathCount D.denseBasis u D.denseBasis_unit _ _ _ _ ha]
  exact (D.functional_apply _).symm

end LabelEvaluator

end VPVNP
end Computability
end OAI
