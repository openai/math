import OAI.LinearAlgebra.SpectralBooks.DiagonalRestriction
import OAI.LinearAlgebra.SpectralBooks.IncrementFormat
import OAI.LinearAlgebra.SpectralBooks.ZariskiCurve

/-! # Restriction of the product of common-label diagonals

The two input diagonals have independent labels `h : Fin q` and `l : Fin L`.
Their tensor product at the specified sites is a sum of pure coordinate
tensors indexed by `(h,l)`. We expand the local coefficient maps of the
increment proof into a many-site tensor restriction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {F : Type*} [Field F]

/-- A basis term of the tensor product of the original `q`-diagonal on the
old sites and the `L`-diagonal on the intersection together with the new site. -/
def incrementSourceBasis (q k m L : ℕ) (s : Fin q × Fin L) :
    ∀ i, incrementOldInput q k m L i
  | .inl _ => s
  | .inr none => s.2
  | .inr (some _) => s.1

private def incrementLocalMatrices {q k m L : ℕ}
    (U : Fin q → Fin q → Fin L → F) (V : Fin k → Fin q → Fin q → Fin L → F)
    (Z : Fin q → Fin L → F) :
    ∀ i, incrementSiteOutput q k m i → incrementOldInput q k m L i → F
  | .inl j => Fin.cases
      (fun y s ↦ if y.1 = s.1 then U y.1 y.2 s.2 else 0)
      (fun j y s ↦ if y.1 = s.1 then V j y.1 y.2 s.2 else 0) j
  | .inr none => Z
  | .inr (some _) => fun (y h : Fin q) ↦ if y = h then 1 else 0

/-- Every member of `commonLabelRestrictions` is an actual restriction by
sitewise linear maps of the specified product of diagonals. -/
theorem isRestriction_of_mem_commonLabelRestrictions {q k m L : ℕ}
    {T : IncrementCoordinate q k m → F} (hT : T ∈ commonLabelRestrictions F q k m L) :
    Crossing.IsRestriction (T ∘ incrementOutputCoordinate q k m)
      (Crossing.basisTensor (incrementSourceBasis q k m L)) := by
  classical
  obtain ⟨U, V, Z, hT⟩ := hT
  apply (Crossing.restriction_basisTensor_iff _ _).mpr
  refine ⟨incrementLocalMatrices U V Z, fun x ↦ ?_⟩
  let c := incrementOutputCoordinate q k m x
  change T c = _
  rw [hT c, Fintype.sum_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_option, Fin.prod_univ_succ]
  change _ = ∑ h : Fin q, ∑ l : Fin L,
    ((if c.h = h then U c.h c.a l else 0) *
      (∏ j, if c.hOther j = h then V j (c.hOther j) (c.v j) l else 0)) *
        (Z c.g l * ∏ j, (if c.hExtra j = h then (1 : F) else 0))
  rw [Finset.sum_eq_single c.h]
  · simp only [ite_true, Fintype.prod_ite_zero, eq_self]
    by_cases ha : ∀ j, c.hOther j = c.h <;> by_cases hb : ∀ j, c.hExtra j = c.h <;>
      simp [IncrementCoordinate.shared, ha, hb]
  · intro h _ hne
    simp [Ne.symm hne]
  · simp

/-- Passing from the explicit locally label-preserving matrices to all local
linear maps also gives an inclusion of their Zariski closures. -/
theorem mem_restrictionClosure_of_mem_commonLabelClosure {q k m L : ℕ}
    {T : IncrementCoordinate q k m → F} (hT : T ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m L)) :
    T ∈ affineZariskiClosure {S | Crossing.IsRestriction (S ∘ incrementOutputCoordinate q k m)
      (Crossing.basisTensor (incrementSourceBasis q k m L))} :=
  fun p hp ↦ hT p fun S hS ↦ hp S (isRestriction_of_mem_commonLabelRestrictions hS)

/-- In the dependent local coordinate format the limiting tensor belongs to
the Zariski closure of the many-site restrictions of the source. -/
theorem mem_siteRestrictionClosure_of_mem_commonLabelClosure {q k m L : ℕ}
    {T : IncrementCoordinate q k m → F} (hT : T ∈ affineZariskiClosure
      (commonLabelRestrictions F q k m L)) :
    T ∘ incrementOutputCoordinate q k m ∈ affineZariskiClosure {S | Crossing.IsRestriction S
      (Crossing.basisTensor (incrementSourceBasis q k m L))} := by
  let f (x : ∀ i, incrementSiteOutput q k m i) : MvPolynomial (IncrementCoordinate q k m) F :=
    MvPolynomial.X (incrementOutputCoordinate q k m x)
  have heval (S : IncrementCoordinate q k m → F) :
      (fun x ↦ MvPolynomial.eval S (f x)) = S ∘ incrementOutputCoordinate q k m := by
    funext x
    simp [f]
  refine heval T ▸ mapsTo_affineZariskiClosure_of_polynomial f (fun S hS ↦ ?_) hT
  simp only [heval]
  exact isRestriction_of_mem_commonLabelRestrictions hS

/-- Border restriction between the two explicit tensor products of diagonals
in the increment argument. The required auxiliary dimension is linear in `q`. -/
theorem commonLabel_borderRestriction (F : Type*) [Field F] [Infinite F] (q k m : ℕ) :
    Crossing.basisTensor (F := F) (incrementTargetBasis q k m) ∈
      affineZariskiClosure {S | Crossing.IsRestriction S (Crossing.basisTensor
        (incrementSourceBasis q k m (2 * (k + 1) * (q - 1) + 1)))} := by
  have ht : Crossing.basisTensor (F := F) (incrementTargetBasis q k m) =
      commonLabelTarget F ∘ incrementOutputCoordinate q k m :=
    funext (incrementTargetBasis_apply F q k m)
  rw [ht]
  exact mem_siteRestrictionClosure_of_mem_commonLabelClosure (commonLabelTarget_mem_closure F q k m)

end SpectralBooks
end LinearAlgebra
end OAI
