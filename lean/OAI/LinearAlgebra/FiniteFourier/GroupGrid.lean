import OAI.LinearAlgebra.FiniteFourier.Cyclic
import OAI.LinearAlgebra.FiniteFourier.GridFactor
import OAI.LinearAlgebra.FiniteFourier.InverseComplexity
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # The character transform is a product of geometric grids

The finite abelian group structure theorem supplies the cyclic factors. Each
factor order divides the group exponent, so primitive roots for all factors
already lie in the given admissible field. Permuting the two index sets
identifies the character table entrywise with the tensor product.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped BigOperators

variable (G K : Type*) [AddCommGroup G] [Fintype G] [Field K]

/-- Data for a cyclic-factor grid, including the row and column bijections
in the coefficient representation of the matrix. -/
structure FourierGrid where
  Axis : Type
  [finiteAxis : Fintype Axis]
  size : Axis → ℕ
  two_le : ∀ i, 2 ≤ size i
  root : Axis → K
  primitive : ∀ i, IsPrimitiveRoot (root i) (size i)
  rows : Character G K ≃ (∀ i, Fin (size i))
  cols : G ≃ (∀ i, Fin (size i))
  reindex_eq : Matrix.reindex rows cols (fourierMatrix G K) =
    gridTensor (fun i => geometricMatrix (size i) (root i))

attribute [instance] FourierGrid.finiteAxis

/-- Every finite abelian group satisfying the manuscript's hypotheses has
a geometric grid presentation over its ground field. -/
theorem exists_fourierGrid (h : Admissible G K) : Nonempty (FourierGrid G K) := by
  classical
  let : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G)) :=
    ⟨h.2, rootsOfUnity.isCyclic _ _⟩
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite (Multiplicative G)
  let A (i : ι) := Multiplicative (ZMod (n i))
  have (i : ι) : NeZero (n i) := NeZero.of_gt (hn i)
  have (i : ι) : HasEnoughRootsOfUnity K (n i) :=
    HasEnoughRootsOfUnity.of_dvd K (cyclicFactor_dvd_exponent e i)
  choose q hq using fun i => HasEnoughRootsOfUnity.exists_primitiveRoot K (n i)
  let axisEquiv (i : ι) : Fin (n i) ≃ A i :=
    (ZMod.finEquiv (n i)).toEquiv.trans Multiplicative.ofAdd
  let C := ((Equiv.piCongrRight axisEquiv).trans e.symm.toEquiv).trans Multiplicative.toAdd
  let R := (Equiv.piCongrRight (fun i => cyclicCharacterEquiv (hq i))).trans
    (((Pi.monoidHomMulEquiv A Kˣ).symm.trans e.symm.monoidHomCongrLeft).toEquiv)
  refine ⟨⟨ι, n, hn, q, hq, R.symm, C.symm, ?_⟩⟩
  ext f x
  change (↑((∏ i, ((cyclicCharacterEquiv (hq i)) (f i)).comp
      (Pi.evalMonoidHom A i)) (e (e.symm (fun i => axisEquiv i (x i))))) : K) = _
  rw [e.apply_symm_apply]
  simp only [MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply,
    Units.coe_prod, gridTensor, geometricMatrix_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (reindex_fourierMatrix_zmod (hq i)) (f i)) (x i)

variable {G K}

omit [Fintype G] in
/-- The primitive roots give distinct evaluation nodes on every axis. -/
theorem FourierGrid.gridFactor (D : FourierGrid G K) (i : D.Axis) :
    GridFactor (geometricMatrix (D.size i) (D.root i)) := by
  apply GridFactor.geometric
  · exact (D.primitive i).ne_zero (by have := D.two_le i; omega)
  · exact fun a b hab => Fin.ext ((D.primitive i).pow_inj a.isLt b.isLt hab)

/-- The total grid size equals the group order. -/
theorem FourierGrid.prod_size (D : FourierGrid G K) : ∏ i, D.size i = Fintype.card G := by
  classical
  simpa [Fintype.card_pi] using (Fintype.card_congr D.cols).symm

open scoped Classical in
/-- Complexity of the grid agrees with both choices of transform direction. -/
theorem FourierGrid.complexity_eq (D : FourierGrid G K) (h : Admissible G K) :
    let C := complexity (gridTensor (fun i => geometricMatrix (D.size i) (D.root i)))
    complexity (fourierMatrix G K) = C ∧ complexity (inverseFourierMatrix G K) = C := by
  dsimp only
  rw [← D.reindex_eq, complexity_reindex, complexity_inverseFourierMatrix G K h]
  exact ⟨rfl, rfl⟩

end

end

end FiniteFourier
end LinearAlgebra
end OAI
