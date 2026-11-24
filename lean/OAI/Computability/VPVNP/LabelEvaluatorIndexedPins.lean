import OAI.Computability.VPVNP.LabelEvaluator
import OAI.Computability.VPVNP.AffineSliceQuery

/-!
# The indexed equations of the label evaluator's actual slice

An enumeration of the original equations is followed by one slot per
coordinate. The slot contains the advised coordinate equation when its mask
bit is set, and the zero polynomial otherwise.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LabelEvaluator

open RadicalCertificate.MonomialIndex MvPolynomial SliceGeometry

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the ground field used to index possible values of pinned coordinates. -/
noncomputable local instance (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _

variable {p : Nat.Primes} {t d m : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin t) ℤ}

/-- The zero or affine pin in one coordinate slot. -/
noncomputable def Model.pinCut (M : Model p d F) (j : Fin t) : AffineCut t (Ground p t d) :=
  if j ∈ M.pins then ⟨-M.values j, Pi.single j 1⟩ else ⟨0, 0⟩

theorem Model.pinCut_polynomial (M : Model p d F) (j : Fin t) :
    (M.pinCut j).polynomial = if j ∈ M.pins then X j - C (M.values j) else 0 := by
  by_cases h : j ∈ M.pins
  · simp only [pinCut, h, ↓reduceIte, AffineCut.polynomial, map_neg]
    rw [Finset.sum_eq_single j]
    · simp [sub_eq_add_neg, add_comm, X]
    · intro i _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  · simp [pinCut, h, AffineCut.polynomial]

/-- Numeric row order of the exact polynomial system presented by the advice. -/
noncomputable def Model.indexedEquations (M : Model p d F) (r : Fin m ≃ ι) :
    Fin (m+t) → MvPolynomial (Fin t) (Ground p t d) :=
  slicedSystem (F ∘ r) M.pinCut

/-- Macaulay queries use the original integer coefficient reader and the
advised pins in the same order as `indexedEquations`. -/
noncomputable def Model.queryData (M : Model p d F)
    (read : Fin m → (Fin t → ℕ) → ℤ) : QueryData t (m+t) (Ground p t d) :=
  slicedQueryData (Fintype.card (Ground p t d)) d (pointCountBound t d) read M.pinCut

theorem Model.queryData_presents (M : Model p d F) (r : Fin m ≃ ι)
    (read : Fin m → (Fin t → ℕ) → ℤ) (hd : 3 ≤ d) (hdeg : ∀ i, (F i).totalDegree ≤ d)
    (hread : ∀ i a, read i a = (F (r i)).coeff (exponentVector a)) :
    (M.queryData read).Presents (M.indexedEquations r) :=
  slicedQueryData_presents (F ∘ r) _ _ _ read M.pinCut rfl hd (fun i => hdeg (r i)) hread

theorem Model.span_indexedEquations (M : Model p d F) (r : Fin m ≃ ι) :
    Ideal.span (Set.range (M.indexedEquations r)) = sliceIdeal p d F M.pins M.values := by
  change Ideal.span _ = Ideal.span (Set.range (pinnedEquations _ _ _))
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (m := m) (n := t) (motive := fun i => M.indexedEquations r i ∈ _) ?_ ?_ i
    · intro j
      exact ⟨Sum.inl (r j), by simp [indexedEquations, slicedSystem, pinnedEquations]⟩
    · intro j
      exact ⟨Sum.inr j, by simp [indexedEquations, slicedSystem, pinnedEquations, pinCut_polynomial]⟩
  · rintro ⟨i | j, rfl⟩
    · exact ⟨(r.symm i).castAdd t, by simp [indexedEquations, slicedSystem, pinnedEquations]⟩
    · exact ⟨j.natAdd m, by simp [indexedEquations, slicedSystem, pinnedEquations, pinCut_polynomial]⟩

end LabelEvaluator

end VPVNP
end Computability
end OAI
