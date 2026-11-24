import OAI.Computability.VPVNP.MacaulayRowIndex
import OAI.Computability.VPVNP.GreedySuffixIndex
import OAI.Computability.VPVNP.EffectiveNullstellensatz
import OAI.Computability.VPVNP.MonomialBasis

/-!
# Numeric basis queries for a finite reduced slice

For an indexed system of equations and a known bound on the finite geometric
zero set, these are the dimension, monomial basis ordinals and matrix entries
from Lemma 8.2. The field cardinality is a numeric input. Correctness uses the
proved effective weak Nullstellensatz and equality of the coefficient routine
with the coefficients of the defining equations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex

open RankQuery MvPolynomial FiniteSlice

/-- Numeric input to the finite-slice queries. -/
structure QueryData (t e : ℕ) (K : Type*) where
  /-- Numeric cardinality of the finite ground field used in the Frobenius queries. -/
  fieldOrder : ℕ
  /-- Supplied upper bound on the total degrees of the indexed defining equations. -/
  degreeBound : ℕ
  /-- Supplied bound on the number of geometric points, also used to enumerate candidate basis
  monomials. -/
  pointBound : ℕ
  /-- Look up the coefficient of an exponent tuple in an indexed defining equation. -/
  getCoeff : Fin e → (Fin t → ℕ) → K

variable {t e : ℕ} {K E : Type*}

namespace QueryData

variable (S : QueryData t e K)

/-- Maximum degree of any target monomial in a multiplication or Frobenius query. -/
def targetDegree := (S.pointBound + 1) * S.fieldOrder

/-- Effective Nullstellensatz certificate degree used to bound the radical membership
computation for the target monomials. -/
def certificateDegree := (2 * max S.degreeBound (S.targetDegree + 1)) ^ (4 * (t + 3))

/-- Ceiling logarithm of the certificate degree in base the ground-field order, giving the
number of Frobenius iterations. -/
def powerExponent := Nat.clog S.fieldOrder S.certificateDegree

/-- Power to which the candidate monomials are raised for the radical membership test. -/
def power := S.fieldOrder ^ S.powerExponent

/-- Degree bound for multipliers in the Macaulay equation rows, obtained by adding the
certificate degree to the powered target degree. -/
def multiplierDegree := S.certificateDegree + S.power * S.targetDegree

/-- Maximum total degree indexed by the columns, allowing a multiplier times any defining
equation. -/
def columnDegree := S.multiplierDegree + S.degreeBound

/-- Coefficient matrix of all bounded monomial multiples of the defining equations, with
entries read from the supplied coefficient lookup. -/
abbrev equations [Zero K] := equationEntry (L := S.multiplierDegree) (D := S.columnDegree) S.getCoeff

/-- Coefficient rows of the powered candidate monomials, indexed by their original ordinals up
to the point bound. -/
abbrev monomials [Zero K] [One K] : Matrix (Fin (size t S.pointBound)) (Fin (size t S.columnDegree)) K :=
  fun j => powerEntry S.power (indexedDigits j)

/-- Rank gained by appending the powered monomial rows to the equation matrix. For a presented
finite slice this computes its reduced coordinate algebra dimension. -/
def dimension [Field K] [DecidableEq K] := suffixDimension S.equations S.monomials

/-- Return the original monomial ordinal for a given position among the rows selected greedily
after the equation rows. -/
def basisIndex [Field K] [DecidableEq K] : Fin S.dimension → Fin (size t S.pointBound) :=
  suffixBasisIndex S.equations S.monomials

/-- The two linear transformations queried in Lemma 8.2. -/
inductive Operation (t : ℕ) where
  | label (i : Fin t)
  | frobenius

/-- Exponent tuple after multiplying by the selected variable or raising the monomial to the
ground-field order. -/
def target (op : Operation t) (a : Fin t → ℕ) : Fin t → ℕ :=
  match op with
  | .label i => fun j => (if j = i then 1 else 0) + a j
  | .frobenius => fun j => S.fieldOrder * a j

/-- Matrix column `j`, row `i`, in dense basis coordinates. -/
def matrixEntry [Field K] [DecidableEq K] (op : Operation t) (i j : Fin S.dimension) : K :=
  entryCoordinate S.multiplierDegree S.columnDegree S.pointBound S.power S.getCoeff
    (S.target op (indexedDigits (S.basisIndex j))) (S.basisIndex i)

variable [Field K] [Fintype K] [DecidableEq K] [Field E] [Algebra K E] [IsAlgClosed E]

/-- Agreement of the numerical field order, degree bound and entry oracle with the equations. -/
structure Presents (F : Fin e → MvPolynomial (Fin t) K) : Prop where
  fieldOrder_eq : S.fieldOrder = Fintype.card K
  degree_ge_three : 3 ≤ S.degreeBound
  degree_le : ∀ i, (F i).totalDegree ≤ S.degreeBound
  coefficient_eq : ∀ i a, S.getCoeff i a = (F i).coeff (exponentVector a)

variable (F : Fin e → MvPolynomial (Fin t) K)

/-- Common zero set of the defining equations in the extension field. -/
def points (E : Type*) [Field E] [Algebra K E] := {x : Fin t → E | ∀ i, aeval x (F i) = 0}

/-- Send a polynomial over the ground field to its class modulo the vanishing ideal of the
common zero set. -/
noncomputable abbrev quotientMap (E : Type*) [Field E] [Algebra K E] :=
  Ideal.Quotient.mkₐ K (vanishingIdeal K (points F E))

/-- Enumerate the classes of candidate monomials in the reduced coordinate algebra using dense
monomial ordinals. -/
noncomputable abbrev listing (E : Type*) [Field E] [Algebra K E]
    (j : Fin (size t S.pointBound)) : CoordinateAlgebra K (points F E) :=
  quotientMap F E (monomialAt t S.pointBound j)

omit [Fintype K] [DecidableEq K] [IsAlgClosed E] in
theorem listing_range :
    Set.range (S.listing F E) =
      MonomialBasis.monomials (coordinateLabel (K := K) (points F E)) S.pointBound := by
  let X := coordinateLabel (K := K) (points F E)
  have value (a : Fin t →₀ ℕ) : quotientMap F E (monomial a 1) = ∏ i, X i ^ a i := by
    unfold quotientMap
    rw [← aeval_coordinateLabel]
    simp [aeval_monomial, Finsupp.prod_fintype, X]
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    let a := enumeration t S.pointBound j
    exact ⟨a.val, by simpa [Finsupp.sum_fintype] using a.prop, (value a.val).symm⟩
  · rintro ⟨f, hf, rfl⟩
    let a : BoundedMonomial t S.pointBound := ⟨exponentVector f, by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]; exact hf⟩
    refine ⟨(enumeration t S.pointBound).symm a, ?_⟩
    simp only [listing, monomialAt, Equiv.apply_symm_apply, value]
    rfl

omit [Fintype K] [DecidableEq K] [IsAlgClosed E] in
theorem listing_first :
    S.listing F E ⟨0, size_pos t S.pointBound⟩ = 1 := by
  simp [listing, monomialAt, enumeration_first, constant]

omit [DecidableEq K] in
private theorem power_eq (h : S.Presents F) :
    S.power = Fintype.card K ^ S.powerExponent := by rw [power, h.fieldOrder_eq]

omit [DecidableEq K] in
private theorem power_ge (h : S.Presents F) : S.certificateDegree ≤ Fintype.card K ^ S.powerExponent := by
  rw [← S.power_eq F h, power, powerExponent]
  apply Nat.le_pow_clog
  rw [h.fieldOrder_eq]; exact Fintype.one_lt_card

omit [DecidableEq K] [Algebra K E] in
private theorem certificateBound (h : S.Presents F) :
    WeakCertificateBound E (Option (Fin e)) (t+1) (max S.degreeBound (S.targetDegree+1)) S.certificateDegree :=
  effective_weakCertificateBound E _ (h.degree_ge_three.trans (le_max_left ..))

omit [DecidableEq K] in
private theorem list_degree (h : S.Presents F) (j : Fin (size t S.pointBound)) :
    (monomialAt t S.pointBound j : MvPolynomial _ K).totalDegree ≤ S.targetDegree := by
  apply (totalDegree_monomial_le _ _).trans
  apply (enumeration t S.pointBound j).prop.trans
  unfold targetDegree
  have hpos : 1 ≤ S.fieldOrder := by rw [h.fieldOrder_eq]; exact Fintype.card_pos
  exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpos)

theorem basisIndex_mem_iff (h : S.Presents F) (j : Fin (size t S.pointBound)) :
    j ∈ Set.range S.basisIndex ↔ j ∈ greedyIndices K (S.listing F E) := by
  have hM (i c) : S.monomials i c = coefficientRow S.columnDegree
      ((monomialAt t S.pointBound i : MvPolynomial _ K) ^ S.power) (enumeration t S.columnDegree c) :=
    powerEntry_indexed_eq _ _ _
  have hW (r c) : S.equations r c = macaulayMatrix F S.multiplierDegree S.columnDegree
      (rowEquiv t e S.multiplierDegree r) (enumeration t S.columnDegree c) :=
    equationEntry_eq F _ h.coefficient_eq r c
  have he := macaulay_greedyIndex_iff F (monomialAt t S.pointBound) (S.power_ge F h)
    h.degree_le (S.list_degree F h) (S.certificateBound (E := E) F h)
    (rowEquiv t e _) (enumeration t _) j
  refine (mem_range_suffixBasisIndex S.equations S.monomials j).trans ?_
  rw [show S.equations = _ from funext fun r => funext (hW r),
      show S.monomials = _ from funext fun i => funext (hM i)]
  dsimp only at he
  rw [← S.power_eq F h] at he
  exact he

omit [Fintype K] [DecidableEq K] [IsAlgClosed E] in
private theorem points_eq_zeroLocus : points F E = zeroLocus E (Ideal.span (Set.range F)) := by
  ext x
  simp [points, zeroLocus_span]

omit [DecidableEq K] [IsAlgClosed E] in
private theorem finiteRank (hfin : (points F E).Finite) (hN : (points F E).ncard ≤ S.pointBound) :
    Module.Finite K (CoordinateAlgebra K (points F E)) ∧
      Module.finrank K (CoordinateAlgebra K (points F E)) ≤ S.pointBound := by
  rw [points_eq_zeroLocus] at hfin hN ⊢
  let := hfin.fintype
  obtain ⟨h, hdim⟩ := coordinateAlgebra_finite_finrank (E := E) (Ideal.span (Set.range F))
  exact ⟨h, hdim.trans (by rwa [← Nat.card_eq_fintype_card])⟩

/-- The matrix-rank algorithm actually indexes a basis of the reduced
coordinate algebra. Its first vector is the unit for a nonempty slice. -/
theorem exists_basis (h : S.Presents F) (hn : (points F E).Nonempty)
    (hfin : (points F E).Finite) (hN : (points F E).ncard ≤ S.pointBound) :
    ∃ b : Module.Basis (Fin S.dimension) K (CoordinateAlgebra K (points F E)),
      (∀ i, b i = S.listing F E (S.basisIndex i)) ∧ ∃ u, u.val = 0 ∧ b u = 1 := by
  let A := CoordinateAlgebra K (points F E)
  let v := S.listing F E
  obtain ⟨hfin', hdim⟩ := S.finiteRank F hfin hN
  let : Module.Finite K A := hfin'
  let : Nonempty (points F E) := hn.to_subtype
  let : Nontrivial A := coordinateAlgebra_nontrivial _
  have hind := suffixBasisIndex_injective S.equations S.monomials
  have himage : Set.range S.basisIndex = (greedyIndices K v : Set _) := Set.ext (S.basisIndex_mem_iff F h)
  let eqv := (Equiv.ofInjective S.basisIndex hind).trans (Set.equivOfEq himage)
  have hi := (linearIndependent_equiv (R := K) (f := fun i : greedyIndices K v => v i.val) eqv).mpr
    (greedyIndices_linearIndepOn K v)
  have hspan : Submodule.span K (Set.range (v ∘ S.basisIndex)) = ⊤ := by
    rw [Set.range_comp, himage]
    have hall := greedyIndices_span_prefix K v (size t S.pointBound)
    have huniv : {i : Fin (size t S.pointBound) | i.val < size t S.pointBound} = Set.univ :=
      Set.eq_univ_of_forall (fun i => i.isLt)
    rw [huniv, Set.inter_univ, Set.image_univ] at hall
    rw [hall, S.listing_range F]
    exact MonomialBasis.degreeSpan_eq_top _ _ (adjoin_coordinateLabel _) hdim
  let b := Module.Basis.mk (v := v ∘ S.basisIndex) hi hspan.ge
  have hb (i) : b i = v (S.basisIndex i) := Module.Basis.mk_apply ..
  let z : Fin (size t S.pointBound) := ⟨0, size_pos ..⟩
  have hz : z ∈ greedyIndices K v := by
    have hempty : Set.Iio z = ∅ := by ext i; simp [z, Fin.le_def]
    rw [mem_greedyIndices, hempty, show v z = 1 from S.listing_first F]
    simp
  obtain ⟨u, hu⟩ := (S.basisIndex_mem_iff F h z).mpr hz
  refine ⟨b, hb, u, ?_, (hb u).trans (hu ▸ S.listing_first F)⟩
  by_contra hne
  let i : Fin S.dimension := ⟨0, u.pos⟩
  have hlt : i < u := Nat.pos_of_ne_zero hne
  have hlt' := suffixBasisIndex_strictMono S.equations S.monomials hlt
  change S.basisIndex i < S.basisIndex u at hlt'
  rw [hu] at hlt'
  exact Nat.not_lt_zero _ hlt'

/-- The size returned by the two rank queries is the reduced algebra dimension. -/
theorem dimension_eq (h : S.Presents F) (hn : (points F E).Nonempty)
    (hfin : (points F E).Finite) (hN : (points F E).ncard ≤ S.pointBound) :
    S.dimension = Module.finrank K (CoordinateAlgebra K (points F E)) := by
  obtain ⟨b, _, _⟩ := S.exists_basis F h hn hfin hN
  simpa using (Module.finrank_eq_card_basis b).symm

/-- Any monomial of degree at most the target-degree bound has the coordinates
returned by the row algorithm, restricted to dense basis ordinals. -/
theorem coordinate_eq_repr (h : S.Presents F)
    (b : Module.Basis (Fin S.dimension) K (CoordinateAlgebra K (points F E)))
    (hb : ∀ i, b i = S.listing F E (S.basisIndex i)) (a : Fin t → ℕ)
    (ha : (monomial (exponentVector a) (1 : K)).totalDegree ≤ S.targetDegree)
    (i : Fin S.dimension) :
    entryCoordinate S.multiplierDegree S.columnDegree S.pointBound S.power S.getCoeff a (S.basisIndex i) =
      b.repr (quotientMap F E (monomial (exponentVector a) 1)) i := by
  let c := entryCoordinate S.multiplierDegree S.columnDegree S.pointBound S.power S.getCoeff a
  let targetPoly : MvPolynomial (Fin t) K := monomial (exponentVector a) 1
  let v := S.listing F E
  have he := entryCoordinate_eq S.multiplierDegree S.columnDegree S.pointBound S.power F S.getCoeff
    h.coefficient_eq a
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← b.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨k,rfl⟩; exact ⟨S.basisIndex k, (hb k).symm⟩
  have hr := macaulayCoordinateQuery_reconstruct F (monomialAt t S.pointBound) targetPoly
    (S.power_ge F h) h.degree_le (S.list_degree F h) ha (S.certificateBound (E := E) F h)
    (rowEquiv t e _) (enumeration t _)
  dsimp only at hr
  rw [← S.power_eq F h] at hr
  have htarget : quotientMap F E targetPoly = ∑ j, c j • v j := by
    dsimp only [c]
    rw [he]
    exact hr (by change _ ∈ Submodule.span K (Set.range v); rw [hspan]; trivial)
  have hz (j : Fin (size t S.pointBound)) (hj : j ∉ Set.range S.basisIndex) : c j = 0 := by
    have hj' := (S.basisIndex_mem_iff (E := E) F h j).not.mp hj
    have hzero := macaulayCoordinateQuery_eq_zero F (monomialAt t S.pointBound) targetPoly
      (S.power_ge F h) h.degree_le (S.list_degree F h) (S.certificateBound (E := E) F h)
      (rowEquiv t e _) (enumeration t _) j hj'
    rw [← S.power_eq F h] at hzero
    dsimp only [c]
    rw [he]
    exact hzero
  have hre : ∑ k, c (S.basisIndex k) • b k = ∑ j, c j • v j := by
    simp only [hb]
    change ∑ x, c (S.basisIndex x) • v (S.basisIndex x) = _
    have hinj : Function.Injective S.basisIndex := suffixBasisIndex_injective S.equations S.monomials
    rw [← Finset.sum_image (s := Finset.univ) (f := fun j => c j • v j) hinj.injOn]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hnot : j ∉ Set.range S.basisIndex := fun ⟨k, hk⟩ => hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
    rw [hz j hnot, zero_smul]
  have hsum := htarget.trans hre.symm
  have hh := congrArg (fun x => b.repr x i) hsum
  simp only [Module.Basis.repr_sum_self] at hh
  exact hh.symm

/-- Multiply by one coordinate or apply the ground-field cardinality power. -/
def Operation.apply {A : Type*} [CommRing A] (op : Operation t) (Q : ℕ) (X : Fin t → A) (v : A) : A :=
  match op with
  | .label i => X i * v
  | .frobenius => v ^ Q

omit [Fintype K] [DecidableEq K] in
private theorem targetPolynomial (op : Operation t) (j : Fin (size t S.pointBound)) :
    monomial (exponentVector (S.target op (indexedDigits j))) (1 : K) =
      op.apply S.fieldOrder MvPolynomial.X (monomialAt t S.pointBound j) := by
  cases op with
  | label i =>
    rw [Operation.apply, monomialAt, X, monomial_mul_monomial, one_mul]
    apply congrArg (fun a : Fin t →₀ ℕ => monomial a (1 : K))
    ext k
    simp [target, exponentVector, indexedDigits_eq, Finsupp.single_apply, eq_comm]
  | frobenius =>
    rw [Operation.apply, monomialAt, monomial_pow, one_pow]
    apply congrArg (fun a : Fin t →₀ ℕ => monomial a (1 : K))
    ext k
    simp [target, exponentVector, indexedDigits_eq]

omit [DecidableEq K] in
private theorem target_degree (h : S.Presents F) (op : Operation t) (j : Fin (size t S.pointBound)) :
    (monomial (exponentVector (S.target op (indexedDigits j))) (1 : K)).totalDegree ≤ S.targetDegree := by
  have hdeg : (monomialAt t S.pointBound j : MvPolynomial _ K).totalDegree ≤ S.pointBound :=
    (totalDegree_monomial_le _ _).trans (enumeration t S.pointBound j).prop
  rw [S.targetPolynomial op j]
  cases op with
  | label i =>
    apply (totalDegree_mul ..).trans
    rw [totalDegree_X]
    have hpos : 1 ≤ S.fieldOrder := by rw [h.fieldOrder_eq]; exact Fintype.card_pos
    exact (Nat.add_le_add_left hdeg 1).trans ((Nat.add_comm 1 _).trans_le (Nat.le_mul_of_pos_right _ hpos))
  | frobenius =>
    apply (totalDegree_pow ..).trans
    unfold targetDegree
    rw [Nat.mul_comm _ S.fieldOrder]
    exact Nat.mul_le_mul_left _ (hdeg.trans (Nat.le_succ _))

/-- The actual matrix-entry routine returns the coefficient of multiplying
the `j`-th basis monomial by a label or raising it to the field cardinality. -/
theorem matrixEntry_eq_repr (h : S.Presents F)
    (b : Module.Basis (Fin S.dimension) K (CoordinateAlgebra K (points F E)))
    (hb : ∀ i, b i = S.listing F E (S.basisIndex i)) (op : Operation t) (i j : Fin S.dimension) :
    S.matrixEntry op i j =
      b.repr (op.apply S.fieldOrder (coordinateLabel (points F E)) (b j)) i := by
  rw [matrixEntry, S.coordinate_eq_repr F h b hb _ (S.target_degree F h op (S.basisIndex j)) i,
    S.targetPolynomial, hb]
  cases op <;> simp [Operation.apply, listing, quotientMap, coordinateLabel]

/-- Lemma 8.2's basis, dimension and coordinate values for the indexed finite
slice. The query functions take the scalar coefficient algorithm as input. -/
theorem finite_slice_coordinate_queries (h : S.Presents F) (hn : (points F E).Nonempty)
    (hfin : (points F E).Finite) (hN : (points F E).ncard ≤ S.pointBound) :
    ∃ b : Module.Basis (Fin S.dimension) K (CoordinateAlgebra K (points F E)),
      (∀ i, b i = S.listing F E (S.basisIndex i)) ∧ (∃ u, u.val = 0 ∧ b u = 1) ∧
      S.dimension = Module.finrank K (CoordinateAlgebra K (points F E)) ∧
      ∀ op i j, S.matrixEntry op i j =
        b.repr (op.apply S.fieldOrder (coordinateLabel (points F E)) (b j)) i := by
  obtain ⟨b, hb, hu⟩ := S.exists_basis F h hn hfin hN
  exact ⟨b, hb, hu, S.dimension_eq F h hn hfin hN, S.matrixEntry_eq_repr F h b hb⟩

end QueryData

end RadicalCertificate.MonomialIndex

end VPVNP
end Computability
end OAI
