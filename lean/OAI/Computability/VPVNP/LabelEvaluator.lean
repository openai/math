import OAI.Computability.VPVNP.EffectiveNullstellensatz
import OAI.Computability.VPVNP.ScalarDescent
import OAI.Computability.VPVNP.SliceEvaluator
import OAI.Computability.VPVNP.SliceField
import OAI.Computability.VPVNP.SliceGeometry

/-!
# Algebraic descent and the matrix-path identity for the label evaluator

For a satisfiable integer label system, Section 8.2 chooses one prime and one
finite algebra with normalized functional for all exponent inputs. In positive
characteristic the prime is the original characteristic. In characteristic
zero its bit length is bounded using the actual coefficient matrix. The
coordinate pins, slice field and monomial list have explicit bounds.
The counted branches below are the matrix-index paths of equation (8.2).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LabelEvaluator

open MvPolynomial RadicalCertificate FiniteSlice SliceGeometry

variable {t : ℕ} {ι : Type*}

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩

/-- Bound on multiplier degrees in the effective polynomial-identity certificate for a system
in `t` variables of degree at most `d`. -/
abbrev multiplierDegree (t d : ℕ) := (2 * d) ^ (4 * (t + 2))
/-- Bound on the number of monomial columns used in the corresponding bounded-degree
coefficient system. -/
abbrev columnCountBound (t d : ℕ) := (multiplierDegree t d + d + 1) ^ t
/-- Uniform upper bound on the number of geometric points in the finite slice. -/
abbrev pointCountBound (t d : ℕ) := (2 * columnCountBound t d) ^ t

/-- Finite extension of the prime field chosen from the column-count bound to supply slice
coordinates. -/
abbrev Ground (p : Nat.Primes) (t d : ℕ) := SliceField.FieldOf p.val (columnCountBound t d)
/-- Algebraic closure of the prime field in which the geometric zero set is taken. -/
abbrev Ambient (p : Nat.Primes) := AlgebraicClosure (ZMod p.val)

/-- Finite enumeration of the label evaluator's slice ground field. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Regard the ambient algebraic closure as an algebra over the finite slice ground field via
its embedding. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Algebra (Ground p t d) (Ambient p) :=
  (SliceField.embed p.val (columnCountBound t d) (Ambient p)).toRingHom.toAlgebra

private theorem aeval_map_int {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (u : Fin t → A) (f : MvPolynomial (Fin t) ℤ) :
    aeval u (map (Int.castRingHom R) f) = eval₂ (Int.castRingHom A) u f := by
  rw [aeval_def, eval₂_map]
  exact congrArg (fun h => eval₂ h u f) (Subsingleton.elim _ _)

/-- The affine ideal obtained by base change and pinning the selected coordinates. -/
noncomputable abbrev sliceIdeal (p : Nat.Primes) (d : ℕ) (F : ι → MvPolynomial (Fin t) ℤ)
    (s : Finset (Fin t)) (a : Fin t → Ground p t d) : Ideal (MvPolynomial (Fin t) (Ground p t d)) :=
  pinnedIdeal (fun i => map (Int.castRingHom (Ground p t d)) (F i)) s a

/-- The slice chosen for this system, including its ordered monomial basis. -/
structure Model (p : Nat.Primes) (d : ℕ) (F : ι → MvPolynomial (Fin t) ℤ) where
  /-- Coordinates fixed by affine equations when selecting this model's finite geometric slice. -/
  pins : Finset (Fin t)
  /-- Ground-field values assigned to the pinned coordinates of the slice. -/
  values : Fin t → Ground p t d
  nonempty : (zeroLocus (Ambient p) (sliceIdeal p d F pins values)).Nonempty
  finite : (zeroLocus (Ambient p) (sliceIdeal p d F pins values)).Finite
  pointCount_le : (zeroLocus (Ambient p) (sliceIdeal p d F pins values)).ncard ≤ pointCountBound t d
  /-- Monomial basis presentation of the coordinate algebra of the finite slice, up to the
  point-count bound. -/
  presentation : SliceEvaluator.Presentation (Ground p t d) (sliceIdeal p d F pins values)
    (pointCountBound t d) (E := Ambient p)
  listing_length_le : presentation.lastIndex + 1 ≤ (pointCountBound t d + 1) ^ t

variable {p : Nat.Primes} {d : ℕ} {F : ι → MvPolynomial (Fin t) ℤ}

/-- Reduced coordinate algebra of the slice defined by the original label equations and the
model's pinned coordinates. -/
abbrev Model.algebra (M : Model p d F) :=
  CoordinateAlgebra (Ground p t d) (zeroLocus (Ambient p) (sliceIdeal p d F M.pins M.values))

/-- Elements of the coordinate algebra represented by the original label variables. -/
noncomputable abbrev Model.labels (M : Model p d F) : Fin t → M.algebra :=
  coordinateLabel (zeroLocus (Ambient p) (sliceIdeal p d F M.pins M.values))

/-- Normalized prime-field linear functional used to evaluate products of the model's labels. -/
noncomputable abbrev Model.functional (M : Model p d F) : M.algebra →ₗ[ZMod p.val] ZMod p.val :=
  M.presentation.functional

theorem Model.finite_algebra (M : Model p d F) : Finite M.algebra := by
  let : Fintype (zeroLocus (Ambient p) (sliceIdeal p d F M.pins M.values)) := M.finite.fintype
  have h := coordinateAlgebra_finite_finrank (E := Ambient p) (sliceIdeal p d F M.pins M.values)
  let : Module.Finite (Ground p t d) M.algebra := h.1
  exact Module.finite_of_finite (Ground p t d)

theorem Model.reduced (M : Model p d F) : IsReduced M.algebra :=
  coordinateAlgebra_isReduced _

theorem Model.solution (M : Model p d F) (i : ι) :
    eval₂ (Int.castRingHom M.algebra) M.labels (F i) = 0 := by
  have hf : map (Int.castRingHom (Ground p t d)) (F i) ∈ sliceIdeal p d F M.pins M.values :=
    Ideal.subset_span ⟨Sum.inl i, rfl⟩
  rw [← aeval_map_int (R := Ground p t d), aeval_coordinateLabel]
  exact equation_eq_zero _ _ hf

theorem Model.functional_one (M : Model p d F) : M.functional 1 = 1 := M.presentation.functional_one

/-- The count uses the same field, basis, labels and functional at every input width. -/
theorem Model.branchCount_mod (M : Model p d F) (width : ℕ) (e : Fin t → ℕ)
    (he : ∀ i, e i < 2 ^ width) :
    (M.presentation.branchCount p.val width e : ZMod p.val) = M.functional (∏ i, M.labels i ^ e i) :=
  M.presentation.branchCount_mod width e he

/-- The slice field and ordered evaluator data exist from a geometric point in
the chosen prime characteristic, with the effective bound discharged. -/
theorem model_of_geometric_solution [Fintype ι] (p : Nat.Primes) (d : ℕ) (hd : 3 ≤ d)
    (F : ι → MvPolynomial (Fin t) ℤ) (hF : ∀ i, (F i).totalDegree ≤ d)
    (x : Fin t → Ambient p) (hx : ∀ i, eval₂ (Int.castRingHom (Ambient p)) x (F i) = 0) :
    Nonempty (Model p d F) := by
  let H := multiplierDegree t d
  let K := Ground p t d
  let G (i : ι) := map (Int.castRingHom K) (F i)
  have hcard : projectionBound t H d < Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact SliceField.field_card_gt _ _
  have hdeg (i : ι) : (G i).totalDegree ≤ d :=
    (Finset.sup_mono (support_map_subset _ _)).trans (hF i)
  have hG (i : ι) : aeval x (G i) = 0 :=
    (aeval_map_int (R := K) x (F i)).trans (hx i)
  obtain ⟨s, a, hn, hfin, hc⟩ := exists_finite_coordinate_slice G hdeg (by omega) hcard
    ⟨x, hG⟩ (effective_weakCertificateBound (Ambient p) _ hd)
  let I := sliceIdeal p d F s a
  let : Fintype (zeroLocus (Ambient p) I) := hfin.fintype
  have : Nonempty (zeroLocus (Ambient p) I) := hn.to_subtype
  have hc' : Fintype.card (zeroLocus (Ambient p) I) ≤ pointCountBound t d := by
    rw [← Nat.card_eq_fintype_card]
    exact hc
  obtain ⟨P, hlist, _⟩ := SliceEvaluator.exists_sliceEvaluator p.val I hc'
  exact ⟨⟨s, a, hn, hfin, hc, P, hlist⟩⟩

/-- A solution in any field of positive characteristic gives the evaluator in
that same characteristic. -/
theorem exists_model_positive [Fintype ι] {k : Type*} [Field k] (p : Nat.Primes) [CharP k p.val]
    (F : ι → MvPolynomial (Fin t) ℤ) (d : ℕ) (hd : 3 ≤ d) (hF : ∀ i, (F i).totalDegree ≤ d)
    (x : Fin t → k) (hx : ∀ i, eval₂ (Int.castRingHom k) x (F i) = 0) :
    Nonempty (Model p d F) := by
  let := ZMod.algebra k p.val
  let G (i : ι) := map (Int.castRingHom (ZMod p.val)) (F i)
  obtain ⟨y, hy⟩ := polynomialSystem_descent (K := Ambient p) (Set.range G) x (by
    rintro _ ⟨i, rfl⟩
    exact (aeval_map_int (R := ZMod p.val) x (F i)).trans (hx i))
  exact model_of_geometric_solution p d hd F hF y fun i =>
    (aeval_map_int (R := ZMod p.val) y (F i)).symm.trans (hy _ ⟨i, rfl⟩)

/-- The chosen prime in characteristic zero admits a geometric solution of the
original integer equations. The effective multiplier bound is proved internally. -/
theorem exists_prime_solution [Fintype ι] {k : Type*} [Field k] [CharZero k]
    (F : ι → MvPolynomial (Fin t) ℤ) (d b : ℕ) (hd : 3 ≤ d) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hcoeff : ∀ i a, ((F i).coeff a).natAbs ≤ 2 ^ b)
    (x : Fin t → k) (hx : ∀ i, eval₂ (Int.castRingHom k) x (F i) = 0) :
    let a := Nat.clog 2 (multiplierDegree t d + d + 1) * t
    ∃ p : Nat.Primes, p.val ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      ∃ y : Fin t → Ambient p, ∀ i, eval₂ (Int.castRingHom (Ambient p)) y (F i) = 0 :=
  CertificateReduction.exists_prime_solution_of_weakCertificateBound F
    (multiplierDegree t d) d b hF hcoeff x hx (fun p => effective_weakCertificateBound (Ambient p) ι hd)

/-- Characteristic-zero descent, with the prime-size bound independent of the
subsequent exponent width and processor program. -/
theorem exists_model_charZero [Fintype ι] {k : Type*} [Field k] [CharZero k]
    (F : ι → MvPolynomial (Fin t) ℤ) (d b : ℕ) (hd : 3 ≤ d) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hcoeff : ∀ i a, ((F i).coeff a).natAbs ≤ 2 ^ b)
    (x : Fin t → k) (hx : ∀ i, eval₂ (Int.castRingHom k) x (F i) = 0) :
    let a := Nat.clog 2 (multiplierDegree t d + d + 1) * t
    ∃ p : Nat.Primes, p.val ≤ 2 ^ (2 * (a + Nat.clog 2 (a + b + 2)) + 1) ∧
      Nonempty (Model p d F) := by
  obtain ⟨p, hp, y, hy⟩ := exists_prime_solution F d b hd hF hcoeff x hx
  exact ⟨p, hp, model_of_geometric_solution p d hd F hF y hy⟩

end LabelEvaluator

end VPVNP
end Computability
end OAI
