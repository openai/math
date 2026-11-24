import Lemmata.FockCircuits.Duality
import OAI.Computability.VPVNP.ShiftedPairing

/-!
# Vacuum pairing in the shifted crossing

The empty-output matrix entry of the finite fermion field is the signed
Pascal minor in Appendix B. Coordinates of exterior products give the
determinant, and the energy-sector enumeration gives the same pairing as the
unimodularity calculation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder I]
  {n : ℕ}

/-- The coordinate of a wedge on an ordered set of modes is a determinant. -/
private theorem wedge_coefficient_det (b : Module.Basis I R M)
    (B : Set.powersetCard I n) (v : Fin n → M) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti R n v) B.val =
      (Matrix.of fun i j ↦ b.repr (v i) (B.val.orderEmbOfFin B.prop j)).det := by
  classical
  have h : (b.ExteriorAlgebra.coord B.val).comp (⋀[R]^n M).subtype =
      (b.exteriorPower n).coord B := by
    apply (b.exteriorPower n).ext
    intro C
    rw [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Subtype.ext_iff]
  change ((b.ExteriorAlgebra.coord B.val).comp (⋀[R]^n M).subtype)
      (exteriorPower.ιMulti R n v) = _
  rw [h, exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

/-- A homogeneous wedge has no coordinate in another occupation degree. -/
private theorem wedge_coefficient_eq_zero_of_card_ne (b : Module.Basis I R M)
    (B : Finset I) (v : Fin n → M) (hB : B.card ≠ n) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti R n v) B = 0 := by
  classical
  have h : (b.ExteriorAlgebra.coord B).comp (⋀[R]^n M).subtype = 0 := by
    apply (b.exteriorPower n).ext
    intro C
    rw [LinearMap.comp_apply, Submodule.subtype_apply, ← ExteriorAlgebra.basis_eq_coe_basis,
      Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.zero_apply]
    exact Finsupp.single_eq_of_ne (fun h ↦ hB (h ▸ C.prop))
  exact LinearMap.congr_fun h (exteriorPower.ιMulti R n v)

open Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open Set.powersetCard
open scoped BigOperators

/-- At the empty output only deletion modes contribute, in increasing source order. -/
private theorem rightProjection_kernel_single_one (R : Type*) [CommRing R] (L : ℕ) (A : Index L) :
    rightProjection R (kernel R L (Pi.single A 1)) =
      ExteriorAlgebra.ιMulti R A.val.card (fun i => finiteVector R L
        (fun k => (negativeCoefficient (A.val.orderEmbOfFin rfl i) k : R))) := by
  classical
  rw [kernel, realize_single, one_smul, map_mul, rightProjection_kernel, mul_one]
  change ExteriorAlgebra.map (rightParticle R)
    (ExteriorAlgebra.map (substitution R L)
      ((Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ExteriorAlgebra A.val)) = _
  rw [ExteriorAlgebra.basis_apply_ofCard (n := A.val.card) _ rfl]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext i
  simp [Function.comp_def, Set.powersetCard.ofFinEmbEquiv_symm_apply]

/-- The vacuum matrix entry on an equal-cardinality sector is the signed
minor of the divided-derivative contraction matrix in Appendix B. -/
theorem vacuum_matrix_det (R : Type*) [CommRing R] {L : ℕ} (A B : Index L)
    (h : B.val.card = A.val.card) :
    matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B =
      (dualSign B.val : R) *
        (Matrix.of fun i j : Fin A.val.card =>
          (negativeCoefficient (A.val.orderEmbOfFin rfl i) (B.val.orderEmbOfFin h j) : R)).det := by
  classical
  change (dualSign B.val : R) * (colourBasis R).repr _ (colourIndex ∅ B.val) = _
  rw [← rightProjection_coefficient, rightProjection_kernel_single_one]
  have coeff := wedge_coefficient_det (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R))
    (Set.powersetCard.ofCard h)
    (fun i => finiteVector R L (fun k => (negativeCoefficient (A.val.orderEmbOfFin rfl i) k : R)))
  rw [show (Fock.basis R).repr _ B.val = _ from coeff]
  congr 2
  ext i j
  change finiteVector R L _ (B.val.orderEmbOfFin h j) = _
  exact finiteVector_apply R L _ ⟨_, Finset.mem_range.mp ((Finset.mem_powerset.mp B.property)
    (B.val.orderEmbOfFin_mem h j))⟩

/-- Unequal occupation sectors have zero vacuum pairing. -/
theorem vacuum_matrix_eq_zero_of_card_ne (R : Type*) [CommRing R] {L : ℕ} (A B : Index L)
    (h : B.val.card ≠ A.val.card) :
    matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B = 0 := by
  classical
  change (dualSign B.val : R) * (colourBasis R).repr _ (colourIndex ∅ B.val) = 0
  rw [← rightProjection_coefficient, rightProjection_kernel_single_one]
  exact mul_eq_zero_of_right _ (wedge_coefficient_eq_zero_of_card_ne _ B.val _ h)


/-- The negative mode gives a sign depending on each row alone. -/
theorem det_negativeCoefficient {m : ℕ} (a b : Fin m → ℕ) :
    (Matrix.of fun i j => Lemmata.FockCircuits.negativeCoefficient (a i) (b j)).det =
      (-1 : ℤ) ^ (∑ i, a i) *
        (Matrix.of fun i j => ((a i + b j).choose (a i) : ℤ)).det := by
  simpa only [Lemmata.FockCircuits.negativeCoefficient, Nat.add_comm, Matrix.of_apply,
    Finset.prod_pow_eq_pow_sum] using
      Matrix.det_mul_column (fun i => (-1 : ℤ) ^ a i)
        (Matrix.of fun i j => ((a i + b j).choose (a i) : ℤ))

/-- With the order reversal from the vacuum contraction, the signed matrix is
exactly the integral pairing in each energy sector of Appendix B. -/
theorem signed_det_negativeCoefficient_eq_sectorPairing {n m bound : ℕ}
    (I J : EnergySector n m bound) :
    (-1 : ℤ) ^ m.choose 2 *
      (Matrix.of fun i j => Lemmata.FockCircuits.negativeCoefficient
        (Set.powersetCard.ofFinEmbEquiv.symm I.val i).val
        (Set.powersetCard.ofFinEmbEquiv.symm J.val j).val).det =
      sectorPairing n m bound I J := by
  rw [det_negativeCoefficient, ← mul_assoc, ← pow_add]
  rfl


/-- The same occupied modes in the larger mode cutoff used for the Wick identity. -/
def sectorIndex {n m L : ℕ} (hn : n ≤ L) (I : Set.powersetCard (Fin n) m) : Index L :=
  ⟨I.val.map Fin.valEmbedding, Finset.mem_powerset.mpr (by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hk
    exact Finset.mem_range.mpr (j.isLt.trans_le hn))⟩

@[simp] theorem sectorIndex_card {n m L : ℕ} (hn : n ≤ L)
    (I : Set.powersetCard (Fin n) m) : (sectorIndex hn I).val.card = m := by
  change (I.val.map Fin.valEmbedding).card = m
  rw [Finset.card_map, I.prop]

/-- Embedding into a larger cutoff preserves the increasing enumeration of the modes. -/
theorem sectorIndex_order {n m L : ℕ} (hn : n ≤ L) (I : Set.powersetCard (Fin n) m) :
    (fun i => ((ofFinEmbEquiv.symm I i).val)) =
      (sectorIndex hn I).val.orderEmbOfFin (sectorIndex_card hn I) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_map.mpr ⟨_, I.val.orderEmbOfFin_mem I.prop i, rfl⟩
  · exact (Fin.valOrderEmb n).strictMono.comp (ofFinEmbEquiv.symm I).strictMono

@[simp] theorem sectorIndex_energy {n m L : ℕ} (hn : n ≤ L)
    (I : Set.powersetCard (Fin n) m) : Lemmata.FockCircuits.doubledEnergy (sectorIndex hn I).val =
      doubledSectorEnergy I := by
  unfold Lemmata.FockCircuits.doubledEnergy doubledSectorEnergy
  rw [← Finset.map_orderEmbOfFin_univ (sectorIndex hn I).val (sectorIndex_card hn I),
    Finset.sum_map]
  simp only [RelEmbedding.coe_toEmbedding, ← sectorIndex_order]

private theorem vacuum_matrix_det_of_card {m L : ℕ} (I J : Index L)
    (hI : I.val.card = m) (hJ : J.val.card = m) :
    matrix ℤ L (Pi.single I 1) ⟨∅, by simp⟩ J = (-1 : ℤ) ^ m.choose 2 *
      (Matrix.of fun i j => negativeCoefficient (I.val.orderEmbOfFin hI i)
          (J.val.orderEmbOfFin hJ j)).det := by
  subst m
  rw [vacuum_matrix_det ℤ I J hJ, dualSign, hJ, Nat.choose_two_right]
  rfl

/-- The vacuum coefficient in the finite operator identity is the paper's
integral pairing, with identical orderings of the rows and columns. -/
theorem vacuum_matrix_sectorPairing {n m bound L : ℕ} (hn : n ≤ L)
    (I J : EnergySector n m bound) :
    matrix ℤ L (Pi.single (sectorIndex hn I.val) 1) ⟨∅, by simp⟩ (sectorIndex hn J.val) =
      sectorPairing n m bound I J := by
  rw [vacuum_matrix_det_of_card _ _ (sectorIndex_card hn I.val) (sectorIndex_card hn J.val),
    ← sectorIndex_order, ← sectorIndex_order]
  exact signed_det_negativeCoefficient_eq_sectorPairing I J

/-- The simultaneous matrix of vacuum entries on all nonempty states of bounded
energy is the integral block matrix from Appendix B. -/
theorem vacuum_matrix_crossingPairing {n bound L : ℕ} (hn : n ≤ L)
    (I J : Σ m : Fin n, EnergySector n (m.val + 1) bound) :
    matrix ℤ L (Pi.single (sectorIndex hn I.2.val) 1) ⟨∅, by simp⟩ (sectorIndex hn J.2.val) =
      crossingPairing n bound I J := by
  obtain ⟨i, I⟩ := I
  obtain ⟨j, J⟩ := J
  by_cases h : i = j
  · subst j
    rw [crossingPairing, Matrix.blockDiagonal'_apply_eq]
    exact vacuum_matrix_sectorPairing hn I J
  · rw [crossingPairing, Matrix.blockDiagonal'_apply_ne
      (fun k : Fin n => sectorPairing n (k.val + 1) bound) I J h]
    apply vacuum_matrix_eq_zero_of_card_ne
    simp only [sectorIndex_card]
    exact fun hij => h (Fin.ext (by omega))

end Crossing

end VPVNP
end Computability
end OAI
