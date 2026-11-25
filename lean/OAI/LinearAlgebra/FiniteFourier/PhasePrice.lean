import OAI.LinearAlgebra.FiniteFourier.Endpoint
import OAI.LinearAlgebra.FiniteFourier.Geometry
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Spectral placement of a controlled phase

The input and output copies of the row label occupy legs 0 and 2.
The two copies of the column label occupy legs 1 and 3. At coincident
positions the spectral placement groups the corresponding coordinate spaces.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

/-- Input row, input column, output row, output column. -/
def phaseLeg (R C : Type) : Fin 4 → Type := ![R, C, R, C]

private def fourLegs {F : Fin 4 → Sort*} (a : F 0) (b : F 1) (c : F 2) (d : F 3) : ∀ i, F i :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun i ↦ i.elim0))))

instance phaseLegFintype (R C : Type) [Fintype R] [Fintype C] (i : Fin 4) :
    Fintype (phaseLeg R C i) := by
  exact fourLegs (F := fun j ↦ Fintype (phaseLeg R C j)) (inferInstance : Fintype R) (inferInstance : Fintype C)
    (inferInstance : Fintype R) (inferInstance : Fintype C) i

variable {K : Type*} [Field K] {R C S D : Type} [Fintype R] [Fintype C] [Fintype S] [Fintype D]

/-- The four-leg tensor associated with an ordinary operator on two registers. -/
def operatorRaw (T : Matrix (R × C) (R × C) K) : Raw (Fin 4) K where
  Leg := phaseLeg R C
  finiteLeg := phaseLegFintype R C
  coeff z := T (z 2, z 3) (z 0, z 1)

/-- The tensor of the diagonal operator associated with `M`. -/
def phaseRaw (M : Matrix R C K) : Raw (Fin 4) K := operatorRaw (phaseWidthZero M)

omit [Fintype R] [Fintype C] in
private theorem phaseEntry_flip (M : Matrix R C K) (r r' : R) (c c' : C) :
    phaseEntry M r' c' r c = phaseEntry M r c r' c' := by
  by_cases hr : r = r' <;> by_cases hc : c = c' <;> simp_all [phaseEntry, eq_comm]

theorem phaseRaw_coeff (M : Matrix R C K) (z : ∀ i, phaseLeg R C i) :
    (phaseRaw M).coeff z = phaseEntry M (z 0) (z 1) (z 2) (z 3) := by
  exact phaseEntry_flip M _ _ _ _

/-- The manuscript's price `P_M(A,B,A',B')`. -/
def fourierPhasePrice (P : SpectralPlacementPrices K Plane) : PhasePrice (Matrix R C K) :=
  fun M x ↦ P.price (phaseRaw M) x

/-- An assignment in the four chosen coordinate bases. -/
def phaseCoordinates (r : R) (c : C) (s : R) (d : C) (i : Fin 4) : phaseLeg R C i :=
  fourLegs r c s d i

theorem phaseRaw_coeff_ne_zero {M : Matrix R C K} : (phaseRaw M).coeff ≠ 0 ↔ M ≠ 0 := by
  apply not_congr
  constructor
  · intro h
    ext r c
    change M r c = (0 : K)
    have he := congrFun h (phaseCoordinates r c r c)
    change phaseEntry M r c r c = 0 at he
    simpa only [phaseEntry, eq_self, and_self, ite_true] using he
  · rintro rfl
    funext z
    change (phaseRaw (0 : Matrix R C K)).coeff (show ∀ i, phaseLeg R C i from z) = 0
    rw [phaseRaw_coeff]
    change (if z 0 = z 2 ∧ z 1 = z 3 then (0 : K) else 0) = 0
    exact ite_self _

/-- A single spectral point at the occupied sites computes every grouped
nonzero phase price for every finite choice of row and column labels. -/
theorem fourierPhasePrice_normalized_group (P : SpectralPlacementPrices K Plane)
    {J : Type} [Fintype J] [Nontrivial J] (x : J ↪ Plane) :
    ∃ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop),
      0 < P.price (Raw.diagonal J K (Fin 2)) x ∧
        ∀ (σ : Fin 4 → J) (R C : Type) [Fintype R] [Fintype C] (M : Matrix R C K), M ≠ 0 →
          fourierPhasePrice P M (x ∘ σ) = rawLogPrice φ
            (P.price (Raw.diagonal J K (Fin 2)) x) ((phaseRaw M).group σ) := by
  obtain ⟨φ, hc, hφ⟩ := P.normalized_group x
  exact ⟨φ, hc, fun σ _ _ _ _ M hM ↦ hφ σ (phaseRaw M) (phaseRaw_coeff_ne_zero.mpr hM)⟩

section Placement

variable {I X : Type} [Fintype I] [Nonempty I] [MetricSpace X]

/-- Either all legs are at a single site or one normalized spectral point
on the original labels computes every tensor after identifying co-located sites. -/
theorem placed_price_normalized_or_collapsed (P : SpectralPlacementPrices K X) (x : I → X) :
    (∀ T : Raw.{0} I K, P.price T x = 0) ∨
      ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ), 0 < c ∧
        ∀ T : Raw.{0} I K, P.price T x = rawLogPrice φ c T := by
  classical
  let J := Set.range x
  let σ : I → J := Set.rangeFactorization x
  let y : J ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  cases subsingleton_or_nontrivial J with
  | inl h =>
    left
    let i₀ : I := Classical.arbitrary I
    have he : x = fun _ ↦ x i₀ := funext fun i ↦ congrArg y (h.elim (σ i) (σ i₀))
    exact fun T ↦ he ▸ P.collapsed T (x i₀)
  | inr h =>
    right
    let : Fintype J := Fintype.ofFinite _
    obtain ⟨φ, hpos, hφ⟩ := P.normalized_group y
    refine ⟨groupSpectralPoint σ Set.rangeFactorization_surjective φ, _, hpos, ?_⟩
    intro T
    by_cases hT : T.coeff = 0
    · rw [P.zero_tensor T hT, rawLogPrice_zero _ _ _ hT]
    · exact hφ σ T hT

theorem placed_price_mono (P : SpectralPlacementPrices K X) (x : I → X)
    {T S : Raw.{0} I K} (h : T.Restricts S) : P.price T x ≤ P.price S x := by
  rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ, c, hc, he⟩
  · simp only [hc, le_refl]
  · rw [he, he]; exact rawLogPrice_mono φ hc.le h

theorem placed_price_class_eq (P : SpectralPlacementPrices K X) (x : I → X)
    {T S : Raw.{0} I K} (h : ofRaw T = ofRaw S) : P.price T x = P.price S x :=
  le_antisymm (placed_price_mono P x (ofRaw_eq_iff.mp h).1)
    (placed_price_mono P x (ofRaw_eq_iff.mp h).2)

theorem placed_price_mul (P : SpectralPlacementPrices K X) (x : I → X)
    (T S : Raw.{0} I K) (hT : T.coeff ≠ 0) (hS : S.coeff ≠ 0) :
    P.price (T.mul S) x = P.price T x + P.price S x := by
  rcases placed_price_normalized_or_collapsed P x with hc | ⟨φ, c, _, he⟩
  · simp [hc]
  · rw [he, he, he, rawLogPrice_mul φ c T S hT hS]

end Placement

omit [Fintype R] [Fintype C] [Fintype S] [Fintype D] in
private theorem phaseEntry_submatrix (M : Matrix R C K) (r : S ≃ R) (c : D ≃ C)
    (s t : S) (d e : D) :
    phaseEntry (M.submatrix r c) s d t e = phaseEntry M (r s) (c d) (r t) (c e) := by
  simp [phaseEntry]

/-- Independent permutations or reindexings of each of the two matrix labels
act by basis changes at all four sites. -/
theorem ofRaw_phaseRaw_submatrix (M : Matrix R C K) (r : S ≃ R) (c : D ≃ C) :
    ofRaw (phaseRaw (M.submatrix r c)) = ofRaw (phaseRaw M) := by
  let e := fourLegs (F := fun i ↦ phaseLeg S D i ≃ phaseLeg R C i) r c r c
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro z
  change phaseEntry (M.submatrix r c) (z 2) (z 3) (z 0) (z 1) =
    phaseEntry M (r (z 2)) (c (z 3)) (r (z 0)) (c (z 1))
  exact phaseEntry_submatrix M r c _ _ _ _

theorem fourierPhasePrice_reindex (P : SpectralPlacementPrices K Plane) (x : Fin 4 → Plane)
    (M : Matrix R C K) (r : S ≃ R) (c : D ≃ C) :
    fourierPhasePrice P (M.submatrix r c) x = fourierPhasePrice P M x :=
  placed_price_class_eq P x (ofRaw_phaseRaw_submatrix M r c)

open scoped Kronecker

omit [Fintype R] [Fintype C] [Fintype S] [Fintype D] in
private theorem phaseEntry_kronecker (M : Matrix R C K) (N : Matrix S D K)
    (r r' : R × S) (c c' : C × D) :
    phaseEntry (M ⊗ₖ N) r c r' c' = phaseEntry M r.1 c.1 r'.1 c'.1 * phaseEntry N r.2 c.2 r'.2 c'.2 := by
  simp only [phaseEntry, Prod.ext_iff, Matrix.kroneckerMap_apply]
  split_ifs <;> simp_all

/-- The phase of a Kronecker product is the sitewise tensor product, with
paired coordinate labels in each of the four local spaces. -/
theorem ofRaw_phaseRaw_kronecker (M : Matrix R C K) (N : Matrix S D K) :
    ofRaw (phaseRaw (M ⊗ₖ N)) = ofRaw (phaseRaw M) * ofRaw (phaseRaw N) := by
  rw [← ofRaw_mul]
  let e := fourLegs (F := fun i ↦ phaseLeg (R × S) (C × D) i ≃
    phaseLeg R C i × phaseLeg S D i) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
  intro z
  change phaseEntry (M ⊗ₖ N) (z 2) (z 3) (z 0) (z 1) =
    phaseEntry M (z 2).1 (z 3).1 (z 0).1 (z 1).1 * phaseEntry N (z 2).2 (z 3).2 (z 0).2 (z 1).2
  exact phaseEntry_kronecker M N _ _ _ _

theorem fourierPhasePrice_kronecker (P : SpectralPlacementPrices K Plane) (x : Fin 4 → Plane)
    (M : Matrix R C K) (N : Matrix S D K) (hM : M ≠ 0) (hN : N ≠ 0) :
    fourierPhasePrice P (M ⊗ₖ N) x = fourierPhasePrice P M x + fourierPhasePrice P N x := by
  exact (placed_price_class_eq P x (ofRaw_phaseRaw_kronecker M N : _ =
    ofRaw ((phaseRaw M).mul (phaseRaw N)))).trans (placed_price_mul P x _ _
      (phaseRaw_coeff_ne_zero.mpr hM) (phaseRaw_coeff_ne_zero.mpr hN))

end

end

end FiniteFourier
end LinearAlgebra
end OAI
