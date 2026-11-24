import OAI.Computability.VPVNP.MacaulayReduction
import OAI.Computability.VPVNP.SliceGeometryPinning

/-!
# Coordinate projections through a Macaulay matrix pencil

Adjoin the equation `X_i - c = 0` to a finite polynomial system, first with
an indeterminate in place of `c`. The resulting Macaulay matrix has entries
of degree at most one in the parameter. Under the uniform weak Nullstellensatz
bound, the coordinate image of the common zero set consists precisely of the
parameters where adjoining the coefficient row of one increases rank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceGeometry

open MvPolynomial RadicalCertificate
open scoped Polynomial

variable {ι : Type*} {t : ℕ}

/-- Adjoin the equation fixing the selected coordinate to the parameter. -/
noncomputable def coordinateEquations {R : Type*} [CommRing R]
    (F : ι → MvPolynomial (Fin t) R) (i : Fin t) (c : R) :
    Option ι → MvPolynomial (Fin t) R :=
  Option.elim' (X i - C c) F

variable {E : Type*} [Field E]

/-- The Macaulay matrix over the univariate parameter ring. -/
noncomputable def coordinatePencil (F : ι → MvPolynomial (Fin t) E) (i : Fin t) (H D : ℕ) :
    Matrix (Option ι × BoundedMonomial t H) (BoundedMonomial t D) E[X] :=
  macaulayMatrix (coordinateEquations (fun j => map Polynomial.C (F j)) i Polynomial.X) H D

/-- Augment the matrix pencil by the constant coefficient row of one. -/
noncomputable def augmentedCoordinatePencil (F : ι → MvPolynomial (Fin t) E) (i : Fin t)
    (H D : ℕ) :
    Matrix (Option (Option ι × BoundedMonomial t H)) (BoundedMonomial t D) E[X] :=
  Option.elim' (fun j => Polynomial.C (coefficientRow D (1 : MvPolynomial (Fin t) E) j))
    (coordinatePencil F i H D)

/-- Specialization at `c` gives exactly the bounded coefficient matrix of the
original equations and the fiber equation `X_i - c`. -/
theorem coordinatePencil_eval (F : ι → MvPolynomial (Fin t) E) (i : Fin t)
    (H D : ℕ) (c : E) :
    (coordinatePencil F i H D).map (Polynomial.eval c) =
      macaulayMatrix (coordinateEquations F i c) H D := by
  let φ := Polynomial.evalRingHom c
  change (macaulayMatrix _ H D).map φ = _
  rw [← CertificateReduction.macaulayMatrix_map]
  congr 1
  funext j
  cases j with
  | none => simp [coordinateEquations, φ]
  | some j =>
    change map φ (map Polynomial.C (F j)) = F j
    rw [map_map, show φ.comp Polynomial.C = RingHom.id E from by ext; simp [φ], map_id]

/-- The indeterminate enters the coordinate fiber equation linearly. -/
theorem coordinatePencil_degree_le (F : ι → MvPolynomial (Fin t) E) (i : Fin t) (H D : ℕ)
    (r : Option ι × BoundedMonomial t H) (j : BoundedMonomial t D) :
    (coordinatePencil F i H D r j).natDegree ≤ 1 := by
  classical
  rw [coordinatePencil, macaulayMatrix_apply]
  split_ifs with h
  · rcases r with ⟨(_ | a), b⟩
    · change ((X i - C (Polynomial.X : E[X])).coeff _).natDegree ≤ 1
      rw [coeff_sub, coeff_X, coeff_C]
      apply (Polynomial.natDegree_sub_le ..).trans (max_le _ _)
      · split_ifs <;> simp
      · split_ifs <;> simp
    · change ((map Polynomial.C (F a)).coeff _).natDegree ≤ 1
      rw [coeff_map]
      simp
  · simp

theorem augmentedCoordinatePencil_degree_le (F : ι → MvPolynomial (Fin t) E) (i : Fin t)
    (H D : ℕ) (r : Option (Option ι × BoundedMonomial t H)) (j : BoundedMonomial t D) :
    (augmentedCoordinatePencil F i H D r j).natDegree ≤ 1 := by
  cases r with
  | none =>
    change (Polynomial.C _).natDegree ≤ 1
    simp
  | some r => exact coordinatePencil_degree_le F i H D r j

private theorem coordinateEquations_degree_le (F : ι → MvPolynomial (Fin t) E)
    {d : ℕ} (hF : ∀ a, (F a).totalDegree ≤ d) (hd : 1 ≤ d) (i : Fin t) (c : E)
    (a : Option ι) : (coordinateEquations F i c a).totalDegree ≤ d := by
  cases a with
  | some a => exact hF a
  | none =>
    apply (mem_restrictTotalDegree ..).mp
    apply Submodule.sub_mem
    · exact (mem_restrictTotalDegree ..).mpr (by simpa using hd)
    · exact (mem_restrictTotalDegree ..).mpr (by simp)

/-- The coordinate image is detected by failure of the bounded certificate
row test. The forward direction holds for any multiplier bound. -/
theorem coordinateImage_iff_row_notMem [Fintype ι] (F : ι → MvPolynomial (Fin t) E)
    (i : Fin t) (c : E) {H d : ℕ} (hF : ∀ a, (F a).totalDegree ≤ d) (hd : 1 ≤ d)
    (bound : WeakCertificateBound E (Option ι) t d H) :
    (∃ x : Fin t → E, (∀ a, eval x (F a) = 0) ∧ x i = c) ↔
      coefficientRow (H + d) (1 : MvPolynomial (Fin t) E) ∉ Submodule.span E
        (Set.range ((coordinatePencil F i H (H + d)).map (Polynomial.eval c)).row) := by
  rw [coordinatePencil_eval]
  let G := coordinateEquations F i c
  have hdeg := coordinateEquations_degree_le F hF hd i c
  constructor
  · rintro ⟨x, hx, hxi⟩ hmem
    have hz (a : Option ι) : aeval x (G a) = 0 := by
      cases a with
      | some a => simpa [G, coordinateEquations] using hx a
      | none => simp [G, coordinateEquations, hxi]
    have h := aeval_eq_zero_of_row_mem G hdeg 1 (by simp) hmem x hz
    simp at h
  · intro hmem
    obtain ⟨x, hx⟩ := CertificateReduction.commonZero_of_one_notMem G H d hdeg hmem bound
    exact ⟨x, fun a => by simpa [G, coordinateEquations] using hx (some a),
      by simpa [G, coordinateEquations, sub_eq_zero] using hx none⟩

/-- Appending the coefficient row of one turns the fiber test into a strict
inequality between the ranks of the two specialized matrix pencils. -/
theorem coordinateImage_iff_rank_lt [Fintype ι] (F : ι → MvPolynomial (Fin t) E)
    (i : Fin t) (c : E) {H d : ℕ} (hF : ∀ a, (F a).totalDegree ≤ d) (hd : 1 ≤ d)
    (bound : WeakCertificateBound E (Option ι) t d H) :
    (∃ x : Fin t → E, (∀ a, eval x (F a) = 0) ∧ x i = c) ↔
      ((coordinatePencil F i H (H + d)).map (Polynomial.eval c)).rank <
        ((augmentedCoordinatePencil F i H (H + d)).map (Polynomial.eval c)).rank := by
  let M := (coordinatePencil F i H (H + d)).map (Polynomial.eval c)
  let N := (augmentedCoordinatePencil F i H (H + d)).map (Polynomial.eval c)
  let v := coefficientRow (H + d) (1 : MvPolynomial (Fin t) E)
  have hrows : Set.range N.row = insert v (Set.range M.row) := by
    have hn : N.row none = v := by
      ext j
      exact Polynomial.eval_C
    ext w
    constructor
    · rintro ⟨(_ | r), rfl⟩
      · exact Or.inl hn
      · exact Or.inr ⟨r, rfl⟩
    · rintro (rfl | ⟨r, rfl⟩)
      · exact ⟨none, hn⟩
      · exact ⟨some r, rfl⟩
  rw [coordinateImage_iff_row_notMem F i c hF hd bound]
  change v ∉ Submodule.span E (Set.range M.row) ↔ M.rank < N.rank
  rw [M.rank_eq_finrank_span_row, N.rank_eq_finrank_span_row, hrows]
  constructor
  · intro hv
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne (Submodule.span_mono (Set.subset_insert _ _)) (fun he => hv ?_)
    rw [he]
    exact Submodule.subset_span (Set.mem_insert _ _)
  · intro hlt hv
    rw [Submodule.span_insert_eq_span hv] at hlt
    exact hlt.false

variable {K : Type*} [Field K] [Algebra K E]

/-- Present the partially pinned set using the original equations and one
potential linear equation per variable. An unused pin contributes zero. -/
noncomputable def pinnedEquations (F : ι → MvPolynomial (Fin t) K) (s : Finset (Fin t))
    (a : Fin t → K) : ι ⊕ Fin t → MvPolynomial (Fin t) K :=
  Sum.elim F fun j => if j ∈ s then X j - C (a j) else 0

/-- Extend the system of partial pins to the geometric field. -/
noncomputable def geometricPinnedEquations (F : ι → MvPolynomial (Fin t) K)
    (s : Finset (Fin t)) (a : Fin t → K) : ι ⊕ Fin t → MvPolynomial (Fin t) E :=
  fun j => map (algebraMap K E) (pinnedEquations F s a j)

theorem geometricPinnedEquations_degree_le (F : ι → MvPolynomial (Fin t) K)
    (s : Finset (Fin t)) (a : Fin t → K) {d : ℕ}
    (hF : ∀ j, (F j).totalDegree ≤ d) (hd : 1 ≤ d) (j : ι ⊕ Fin t) :
    (geometricPinnedEquations (E := E) F s a j).totalDegree ≤ d := by
  refine (Finset.sup_mono (support_map_subset (algebraMap K E) (pinnedEquations F s a j))).trans ?_
  change (pinnedEquations F s a j).totalDegree ≤ d
  cases j with
  | inl j => exact hF j
  | inr j =>
    by_cases hj : j ∈ s
    · simpa only [pinnedEquations, Sum.elim_inr, ite_eq_left hj, coordinateEquations, Option.elim'_none] using
        coordinateEquations_degree_le F hF hd j (a j) none
    · simp [pinnedEquations, hj]

/-- The fixed-size pinned equation list cuts out precisely the partially pinned
geometric point set. -/
theorem mem_pinnedPoints_iff (F : ι → MvPolynomial (Fin t) K)
    (s : Finset (Fin t)) (a : Fin t → K) (x : Fin t → E) :
    x ∈ pinnedPoints {y : Fin t → E | ∀ j, aeval y (F j) = 0} s a ↔
      ∀ j, eval x (geometricPinnedEquations F s a j) = 0 := by
  have he (j : ι ⊕ Fin t) :
      eval x (geometricPinnedEquations F s a j) = aeval x (pinnedEquations F s a j) := by
    rw [geometricPinnedEquations, eval_map, aeval_def]
  simp_rw [he]
  constructor
  · rintro ⟨hF, hs⟩ (j | j)
    · exact hF j
    · by_cases hj : j ∈ s
      · simp [pinnedEquations, hj, hs j hj]
      · simp [pinnedEquations, hj]
  · intro h
    refine ⟨fun j => h (.inl j), fun j hj => ?_⟩
    simpa [pinnedEquations, hj, sub_eq_zero] using h (.inr j)

/-- Rank criterion for each coordinate of each partial pin, with the same
certificate bound and index types at every stage of the slicing procedure. -/
theorem mem_pinnedCoordinateImage_iff_rank_lt [Fintype ι] (F : ι → MvPolynomial (Fin t) K)
    (s : Finset (Fin t)) (a : Fin t → K) (i : Fin t) (c : E) {H d : ℕ}
    (hF : ∀ j, (F j).totalDegree ≤ d) (hd : 1 ≤ d)
    (bound : WeakCertificateBound E (Option (ι ⊕ Fin t)) t d H) :
    let G := geometricPinnedEquations (E := E) F s a
    c ∈ coordinateImage (pinnedPoints {y : Fin t → E | ∀ j, aeval y (F j) = 0} s a) i ↔
      ((coordinatePencil G i H (H + d)).map (Polynomial.eval c)).rank <
        ((augmentedCoordinatePencil G i H (H + d)).map (Polynomial.eval c)).rank := by
  dsimp only
  rw [← coordinateImage_iff_rank_lt _ i c (geometricPinnedEquations_degree_le F s a hF hd) hd bound]
  change (∃ x, x ∈ pinnedPoints _ s a ∧ x i = c) ↔ _
  simp_rw [mem_pinnedPoints_iff]

end SliceGeometry

end VPVNP
end Computability
end OAI
