import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Fin

/-!
# The integral pairing for shifted crossing

Appendix B of *VP and VNP differ over every field* gives the coefficient of the
full fermionic contraction as a signed binomial determinant. In each sector of
fixed particle number, Cauchy–Binet expresses this determinant as a Gram matrix
of Pascal minors. A nonzero minor can only lower the energy of the intermediate
index. This proves that the pairing on the entire energy cutoff is unimodular.

Its integral inverse acts on the first operator index in both crossing terms.
The two factorization index sets can have different sizes, and each gives a
flattening rank bound after specialization to an arbitrary field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

section

open Set

variable {R I J K : Type*} [CommRing R] [LinearOrder I] [LinearOrder J] [LinearOrder K]

/-- Matrix of the size-`m` minors, with each index set in increasing order. -/
noncomputable def compound (m : ℕ) (A : Matrix I J R) :
    Matrix (powersetCard I m) (powersetCard J m) R :=
  fun s t ↦ (A.submatrix (powersetCard.ofFinEmbEquiv.symm s)
    (powersetCard.ofFinEmbEquiv.symm t)).det

/-- Transposition exchanges the two index sets of every minor. -/
theorem compound_transpose (m : ℕ) (A : Matrix I J R) :
    compound m A.transpose = (compound m A).transpose := by
  ext s t
  exact Matrix.det_transpose _

variable [Fintype I] [Fintype J] [Fintype K]

private theorem compound_eq_toMatrix (m : ℕ) (A : Matrix I J R) :
    compound m A = LinearMap.toMatrix ((Pi.basisFun R J).exteriorPower m)
      ((Pi.basisFun R I).exteriorPower m) (exteriorPower.map m A.mulVecLin) := by
  ext s t
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  simp [Module.Basis.coord_apply, Pi.basisFun_apply]

/-- Cauchy–Binet over an arbitrary commutative ring. -/
theorem compound_mul (m : ℕ) (A : Matrix I J R) (B : Matrix J K R) :
    compound m (A * B) = compound m A * compound m B := by
  rw [compound_eq_toMatrix, compound_eq_toMatrix, compound_eq_toMatrix, Matrix.mulVecLin_mul,
    exteriorPower.map_comp, LinearMap.toMatrix_comp _ ((Pi.basisFun R J).exteriorPower m)]

end

/-- If an integer Pascal minor is nonzero, each selected column index is at
most the corresponding selected row index. -/
theorem pascalMinor_support {m n : ℕ} (r c : Fin m → Fin n)
    (hr : StrictMono r) (hc : StrictMono c)
    (hdet : Matrix.det (Matrix.of fun i j => ((r i).val.choose (c j).val : ℤ)) ≠ 0) :
    ∀ k, c k ≤ r k := by
  classical
  intro k
  by_contra! hbad
  apply hdet
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  simp only [Matrix.of_apply]
  suffices ∃ i, σ i ≤ k ∧ k ≤ i by
    obtain ⟨i, hrow, hcol⟩ := this
    have hlt : r (σ i) < c i :=
      (hr.monotone hrow).trans_lt (hbad.trans_le (hc.monotone hcol))
    have hzero : ((r (σ i)).val.choose (c i).val : ℤ) = 0 := by
      simp [Nat.choose_eq_zero_of_lt hlt]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, smul_zero]
  by_contra! hall
  have maps : Set.MapsTo σ.symm (Finset.Iic k : Finset (Fin m)) (Finset.Iio k) := by
    intro j hj
    apply Finset.mem_Iio.mpr
    apply hall (σ.symm j)
    simpa using (Finset.mem_Iic.mp hj)
  have hcard := Finset.card_le_card_of_injOn σ.symm maps σ.symm.injective.injOn
  simp at hcard

/-- Every principal minor of the integer Pascal matrix has determinant one. -/
theorem pascalMinor_diagonal {m n : ℕ} (r : Fin m → Fin n) (hr : StrictMono r) :
    Matrix.det (Matrix.of fun i j => ((r i).val.choose (r j).val : ℤ)) = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp
  · intro i j hij
    have hij' : (r i).val < (r j).val := hr (show i < j from hij)
    simp [Nat.choose_eq_zero_of_lt hij']

open scoped BigOperators Matrix
open Set.powersetCard

/-- The matrix of binomial coefficients before taking exterior powers. -/
def pascalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (i.val.choose j.val : ℤ)

/-- The Gram matrix of Pascal's triangle gives the contraction kernel. -/
theorem pascalGram (n : ℕ) (i j : Fin n) :
    (pascalMatrix n * (pascalMatrix n)ᵀ) i j = ((i.val + j.val).choose i.val : ℤ) := by
  change ∑ k : Fin n, (i.val.choose k.val : ℤ) * (j.val.choose k.val : ℤ) = _
  norm_cast
  rw [Fin.sum_univ_eq_sum_range (fun k => i.val.choose k * j.val.choose k), add_comm i.val j.val,
    Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = ∑ k ∈ Finset.range (i.val + 1), i.val.choose k * j.val.choose k := by
      refine (Finset.sum_subset (Finset.range_mono i.isLt) ?_).symm
      intro k _ hk
      rw [Nat.choose_eq_zero_of_lt (by simpa [Finset.mem_range] using hk), zero_mul]
    _ = _ := Finset.sum_congr rfl fun k hk => by
      rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hk), mul_comm]

/-- A sector of Fock states with fixed occupation number and bounded doubled energy. -/
def doubledSectorEnergy {n m : ℕ} (I : Set.powersetCard (Fin n) m) : ℕ :=
  ∑ k : Fin m, (2 * (ofFinEmbEquiv.symm I k).val + 1)

/-- Doubling removes all half-integral mode energies in a fixed occupation sector. -/
theorem doubledSectorEnergy_eq {n m : ℕ} (I : Set.powersetCard (Fin n) m) :
    doubledSectorEnergy I = 2 * ∑ k : Fin m, (ofFinEmbEquiv.symm I k).val + m := by
  simp [doubledSectorEnergy, Finset.sum_add_distrib, Finset.mul_sum]

/-- For a pair of equally large, nonempty blocks the pole degree `L = h + h' - 1`
is an integer. The numerator in its doubled-energy formula is exactly even. -/
theorem sectorPoleDegree_eq {n m : ℕ} (I J : Set.powersetCard (Fin n) (m + 1)) :
    2 * ((doubledSectorEnergy I + doubledSectorEnergy J) / 2 - 1) + 2 =
      doubledSectorEnergy I + doubledSectorEnergy J := by
  rw [doubledSectorEnergy_eq, doubledSectorEnergy_eq]
  omega

/-- The states with exactly `m` occupied modes among the first `n` and doubled energy at most
`bound`. -/
abbrev EnergySector (n m bound : ℕ) :=
  {I : Set.powersetCard (Fin n) m // doubledSectorEnergy I ≤ bound}

private theorem sectorEnergy_le {n m : ℕ} {I J : Set.powersetCard (Fin n) m}
    (h : ∀ k, ofFinEmbEquiv.symm J k ≤ ofFinEmbEquiv.symm I k) :
    doubledSectorEnergy J ≤ doubledSectorEnergy I :=
  Finset.sum_le_sum fun k _ => by
    have hh : (ofFinEmbEquiv.symm J k).val ≤ (ofFinEmbEquiv.symm I k).val := h k
    omega

private theorem sectorEnergy_lt {n m : ℕ} {I J : Set.powersetCard (Fin n) m}
    (hne : J ≠ I) (h : ∀ k, ofFinEmbEquiv.symm J k ≤ ofFinEmbEquiv.symm I k) :
    doubledSectorEnergy J < doubledSectorEnergy I := by
  obtain ⟨k, hk⟩ : ∃ k, ofFinEmbEquiv.symm J k < ofFinEmbEquiv.symm I k := by
    by_contra! hall
    apply hne
    apply ofFinEmbEquiv.symm.injective
    ext k
    exact le_antisymm (h k) (hall k)
  apply Finset.sum_lt_sum
  · intro k _
    have hh : (ofFinEmbEquiv.symm J k).val ≤ (ofFinEmbEquiv.symm I k).val := h k
    omega
  · refine ⟨k, Finset.mem_univ _, ?_⟩
    change (ofFinEmbEquiv.symm J k).val < (ofFinEmbEquiv.symm I k).val at hk
    omega

/-- Pascal minors on the energy downset of a fixed occupation number. -/
noncomputable def sectorPascal (n m bound : ℕ) :
    Matrix (EnergySector n m bound) (EnergySector n m bound) ℤ :=
  (compound m (pascalMatrix n)).submatrix Subtype.val Subtype.val

private theorem pascalSupport {n m : ℕ} {I J : Set.powersetCard (Fin n) m}
    (h : compound m (pascalMatrix n) I J ≠ 0) :
    ∀ k, ofFinEmbEquiv.symm J k ≤ ofFinEmbEquiv.symm I k :=
  pascalMinor_support _ _ (ofFinEmbEquiv.symm I).strictMono (ofFinEmbEquiv.symm J).strictMono h

/-- No intermediate index outside the energy cutoff contributes to Cauchy–Binet. -/
theorem sectorPascal_gram (n m bound : ℕ) :
    (compound m (pascalMatrix n * (pascalMatrix n)ᵀ)).submatrix
        (fun I : EnergySector n m bound => I.val) Subtype.val =
      sectorPascal n m bound * (sectorPascal n m bound)ᵀ := by
  classical
  rw [compound_mul, compound_transpose]
  ext I J
  simp only [sectorPascal, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  let good := fun K : Set.powersetCard (Fin n) m => doubledSectorEnergy K ≤ bound
  rw [← Fintype.sum_subtype_add_sum_subtype good]
  suffices ∑ K : {K // ¬good K},
      compound m (pascalMatrix n) I.val K.val * compound m (pascalMatrix n) J.val K.val = 0 by
    rw [this, add_zero]
  apply Finset.sum_eq_zero
  intro K _
  have hzero : compound m (pascalMatrix n) I.val K.val = 0 := by
    by_contra hn
    exact K.property ((sectorEnergy_le (pascalSupport hn)).trans I.property)
  rw [hzero, zero_mul]

/-- The restricted matrix of Pascal minors has determinant one, including ties in energy. -/
theorem sectorPascal_det (n m bound : ℕ) : (sectorPascal n m bound).det = 1 := by
  classical
  let grade : EnergySector n m bound → ℕᵒᵈ := fun I => doubledSectorEnergy I.val
  have htri : (sectorPascal n m bound).BlockTriangular grade := by
    intro I J hlt
    by_contra hn
    exact (not_lt_of_ge (sectorEnergy_le (pascalSupport hn))) hlt
  have hblocks (k : ℕᵒᵈ) : (sectorPascal n m bound).toSquareBlock grade k = 1 := by
    ext I J
    rw [Matrix.one_apply]
    split_ifs with hIJ
    · subst J
      exact pascalMinor_diagonal _ (ofFinEmbEquiv.symm I.val.val).strictMono
    · by_contra hn
      have hne : J.val.val ≠ I.val.val :=
        fun heq => hIJ (Subtype.ext (Subtype.ext heq.symm))
      have hlt := sectorEnergy_lt hne (pascalSupport hn)
      have heq : doubledSectorEnergy I.val.val = doubledSectorEnergy J.val.val :=
        I.property.trans J.property.symm
      omega
  simp [htri.det, hblocks]

/-- The sign of a full matching in the order of the fermionic fields of Appendix B. -/
def crossingRowSign {n m : ℕ} (I : Set.powersetCard (Fin n) m) : ℤ :=
  (-1) ^ (m.choose 2 + ∑ k : Fin m, (ofFinEmbEquiv.symm I k).val)

/-- The signed determinant of the full-contraction coefficients in equation (B.1),
restricted to an energy sector. -/
noncomputable def sectorPairing (n m bound : ℕ) :
    Matrix (EnergySector n m bound) (EnergySector n m bound) ℤ :=
  fun I J => crossingRowSign I.val *
    (compound m (fun i j : Fin n => ((i.val + j.val).choose i.val : ℤ))) I.val J.val

/-- Equation (B.1)'s integral pairing in each fixed-cardinality sector is unimodular. -/
theorem sectorPairing_isUnit (n m bound : ℕ) : IsUnit (sectorPairing n m bound) := by
  classical
  have hgram : (fun i j : Fin n => ((i.val + j.val).choose i.val : ℤ)) =
      pascalMatrix n * (pascalMatrix n)ᵀ := by
    ext i j
    exact (pascalGram n i j).symm
  have hfactor : sectorPairing n m bound =
      Matrix.diagonal (fun I : EnergySector n m bound => crossingRowSign I.val) *
        (sectorPascal n m bound * (sectorPascal n m bound)ᵀ) := by
    rw [← sectorPascal_gram]
    ext I J
    rw [Matrix.diagonal_mul]
    simp only [sectorPairing, hgram, Matrix.submatrix_apply]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, sectorPascal_det,
    Matrix.det_diagonal, one_mul, mul_one]
  exact IsUnit.prod_univ_iff.mpr fun I => isUnit_one.neg.pow _

/-- The pairing on all nonempty states uses the positive particle-number sectors as blocks. -/
noncomputable def crossingPairing (n bound : ℕ) :
    Matrix (Σ m : Fin n, EnergySector n (m.val + 1) bound)
      (Σ m : Fin n, EnergySector n (m.val + 1) bound) ℤ :=
  Matrix.blockDiagonal' fun m => sectorPairing n (m.val + 1) bound

/-- The simultaneous pairing on every nonempty state under the energy cutoff has
an integral inverse. -/
theorem crossingPairing_isUnit (n bound : ℕ) : IsUnit (crossingPairing n bound) :=
  (Pi.isUnit_iff.mpr fun m : Fin n => sectorPairing_isUnit n (m.val + 1) bound).map
    (Matrix.blockDiagonal'RingHom (fun m : Fin n => EnergySector n (m.val + 1) bound) ℤ)

/-- Enumerating the modes in increasing order preserves the total doubled energy. -/
theorem doubledSectorEnergy_eq_sum {n m : ℕ} (I : Set.powersetCard (Fin n) m) :
    doubledSectorEnergy I = ∑ i ∈ I.val, (2 * i.val + 1) := by
  have hc : I.val.card = m := I.prop
  calc
    doubledSectorEnergy I =
        ∑ i ∈ Finset.univ.map (I.val.orderEmbOfFin hc).toEmbedding, (2 * i.val + 1) := by
      rw [Finset.sum_map]
      rfl
    _ = _ := by rw [Finset.map_orderEmbOfFin_univ I.val hc]

/-- A nonvacuum fermionic state in the energy ball of doubled radius `B`. -/
abbrev BoundedState (B : ℕ) :=
  {S : Finset ℕ // S.Nonempty ∧ ∑ i ∈ S, (2 * i + 1) ≤ B}

private def sectorState {B : ℕ} (s : Σ m : Fin B, EnergySector B (m.val + 1) B) :
    BoundedState B := by
  rcases s with ⟨m, I, hI⟩
  refine ⟨I.val.map Fin.valEmbedding, Finset.card_pos.mp ?_, ?_⟩
  · rw [Finset.card_map, I.prop]
    omega
  · rw [Finset.sum_map]
    exact (doubledSectorEnergy_eq_sum I ▸ hI)

private theorem sectorState_injective (B : ℕ) : Function.Injective (@sectorState B) := by
  rintro ⟨m, I, hI⟩ ⟨k, J, hJ⟩ h
  have hval : I.val = J.val := Finset.map_injective Fin.valEmbedding (congrArg Subtype.val h)
  have hmk : m = k := Fin.ext (by simpa [I.prop, J.prop] using congrArg Finset.card hval)
  subst k
  have hIJ : I = J := Subtype.ext hval
  subst J
  rfl

private theorem sectorState_surjective (B : ℕ) : Function.Surjective (@sectorState B) := by
  rintro ⟨S, hS, hEnergy⟩
  have hmode (i : ℕ) (hi : i ∈ S) : i < B := by
    have hle := Finset.single_le_sum (f := fun j => 2 * j + 1) (fun _ _ => Nat.zero_le _) hi
    omega
  have hpos : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : S.card ≤ B := by
    simpa using (Finset.card_le_univ (S.attachFin hmode))
  let m : Fin B := ⟨S.card - 1, by omega⟩
  let I : Set.powersetCard (Fin B) (m.val + 1) := ⟨S.attachFin hmode, by
    change (S.attachFin hmode).card = S.card - 1 + 1
    rw [Finset.card_attachFin]
    omega⟩
  have hI : doubledSectorEnergy I ≤ B := by
    rw [doubledSectorEnergy_eq_sum]
    change ∑ i ∈ S.attachFin hmode, (2 * i.val + 1) ≤ B
    have h := Finset.sum_map (S.attachFin hmode) Fin.valEmbedding (fun i : ℕ => 2 * i + 1)
    rw [Finset.map_valEmbedding_attachFin] at h
    exact h ▸ hEnergy
  exact ⟨⟨m, I, hI⟩, Subtype.ext (Finset.map_valEmbedding_attachFin hmode)⟩

/-- Decompose the energy-bounded nonvacuum states into blocks by occupation number. -/
noncomputable def boundedStateEquivSectors (B : ℕ) :
    BoundedState B ≃ (Σ m : Fin B, EnergySector B (m.val + 1) B) :=
  (Equiv.ofBijective sectorState ⟨sectorState_injective B, sectorState_surjective B⟩).symm

@[simp]
theorem boundedStateEquivSectors_symm_val {B : ℕ}
    (s : Σ m : Fin B, EnergySector B (m.val + 1) B) :
    ((boundedStateEquivSectors B).symm s).val = s.2.val.val.map Fin.valEmbedding := by
  cases s with | mk m I => cases I; rfl

theorem boundedStateEquivSectors_modes {B : ℕ} (S : BoundedState B) :
    ((boundedStateEquivSectors B S).2.val.val.map Fin.valEmbedding) = S.val := by
  rw [← boundedStateEquivSectors_symm_val, Equiv.symm_apply_apply]

theorem boundedStateEquivSectors_card {B : ℕ} (S : BoundedState B) :
    (boundedStateEquivSectors B S).1.val + 1 = S.val.card := by
  rw [← boundedStateEquivSectors_modes S, Finset.card_map]
  exact (boundedStateEquivSectors B S).2.val.prop.symm

noncomputable instance (B : ℕ) : Fintype (BoundedState B) :=
  Fintype.ofEquiv _ (boundedStateEquivSectors B).symm

/-- The full integral pairing on the nonempty finite subsets of natural modes of
doubled energy at most `B`. -/
noncomputable def boundedStatePairing (B : ℕ) : Matrix (BoundedState B) (BoundedState B) ℤ :=
  Matrix.reindexRingEquiv ℤ (boundedStateEquivSectors B).symm (crossingPairing B B)

/-- An integral inverse exists for every energy cutoff in the infinite-mode indexing. -/
theorem boundedStatePairing_isUnit (B : ℕ) : IsUnit (boundedStatePairing B) :=
  (crossingPairing_isUnit B B).map (Matrix.reindexRingEquiv ℤ (boundedStateEquivSectors B).symm)

private theorem sectorNaturalModes {B m : ℕ} (I : EnergySector B m B) {S : Finset ℕ}
    (hS : I.val.val.map Fin.valEmbedding = S) (hc : S.card = m) :
    (fun k : Fin m => (ofFinEmbEquiv.symm I.val k).val) = S.orderEmbOfFin hc := by
  refine Finset.orderEmbOfFin_unique hc (fun k => ?_) ?_
  · rw [← hS]
    apply Finset.mem_map.mpr
    refine ⟨ofFinEmbEquiv.symm I.val k, ?_, rfl⟩
    exact (mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mp ⟨k, rfl⟩
  · exact fun a b hab => (ofFinEmbEquiv.symm I.val).strictMono hab

/-- On states with different occupation numbers the full-contraction pairing vanishes. -/
theorem boundedStatePairing_eq_zero_of_card_ne {B : ℕ} (S T : BoundedState B)
    (h : S.val.card ≠ T.val.card) : boundedStatePairing B S T = 0 := by
  have hne : (boundedStateEquivSectors B S).1 ≠ (boundedStateEquivSectors B T).1 := by
    intro heq
    exact h (by rw [← boundedStateEquivSectors_card S, ← boundedStateEquivSectors_card T, heq])
  change crossingPairing B B (boundedStateEquivSectors B S) (boundedStateEquivSectors B T) = 0
  exact Matrix.blockDiagonal'_apply_ne _ _ _ hne

/-- In the natural-mode indexing, the integral pairing is the signed determinant
of the binomial contraction kernel, in increasing order on both lists. -/
theorem boundedStatePairing_eq_det {B m : ℕ} (S T : BoundedState B)
    (hS : S.val.card = m) (hT : T.val.card = m) :
    boundedStatePairing B S T =
      (-1 : ℤ) ^ (m.choose 2 + ∑ i : Fin m, S.val.orderEmbOfFin hS i) *
        Matrix.det (Matrix.of fun i j : Fin m =>
          ((S.val.orderEmbOfFin hS i + T.val.orderEmbOfFin hT j).choose
            (S.val.orderEmbOfFin hS i) : ℤ)) := by
  have hSM := boundedStateEquivSectors_modes S
  have hTM := boundedStateEquivSectors_modes T
  have hSC := (boundedStateEquivSectors_card S).trans hS
  have hTC := (boundedStateEquivSectors_card T).trans hT
  change crossingPairing B B (boundedStateEquivSectors B S) (boundedStateEquivSectors B T) = _
  generalize (boundedStateEquivSectors B S) = u at *
  generalize (boundedStateEquivSectors B T) = v at *
  obtain ⟨a, I⟩ := u
  obtain ⟨b, J⟩ := v
  have hab : a = b := Fin.ext (by simpa using hSC.trans hTC.symm)
  subst b
  change a.val + 1 = m at hSC
  cases hSC
  have hr := sectorNaturalModes I hSM hS
  have hc := sectorNaturalModes J hTM hT
  rw [crossingPairing, Matrix.blockDiagonal'_apply_eq]
  change (-1 : ℤ) ^ ((a.val + 1).choose 2 + ∑ i : Fin (a.val + 1),
      (ofFinEmbEquiv.symm I.val i).val) *
        Matrix.det (Matrix.of fun i j : Fin (a.val + 1) =>
          (((ofFinEmbEquiv.symm I.val i).val + (ofFinEmbEquiv.symm J.val j).val).choose
            (ofFinEmbEquiv.symm I.val i).val : ℤ)) = _
  simp_rw [← hr, ← hc]

private theorem mixFactors {I K : Type*} [Fintype I] [Fintype K]
    (w : I → ℤ) (f : K → I → ℤ) (g : K → ℤ) :
    ∑ k, (∑ i, w i * f k i) * g k = ∑ i, w i * ∑ k, f k i * g k := by
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Apply the inverse of the integral pairing on the first index in both crossing
families. This preserves the original two index sets of factors. -/
theorem normalizeCrossing {X Y K L : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq Y] [Fintype K] [Fintype L]
    (a b : K → X → Y → ℤ) (c d : L → X → Y → ℤ)
    (G : Matrix X X ℤ) (hG : IsUnit G)
    (h : ∀ i j α β, ∑ k, a k i α * b k j β + ∑ l, c l i β * d l j α
      = G i j * (if α = β then 1 else 0)) :
    ∃ (a' : K → X → Y → ℤ) (c' : L → X → Y → ℤ),
      ∀ i j α β, ∑ k, a' k i α * b k j β + ∑ l, c' l i β * d l j α
        = (if i = j then 1 else 0) * (if α = β then 1 else 0) := by
  obtain ⟨u, rfl⟩ := hG
  let H : Matrix X X ℤ := ↑u⁻¹
  refine ⟨fun k i α => ∑ t, H i t * a k t α, fun l i β => ∑ t, H i t * c l t β, ?_⟩
  intro i j α β
  rw [mixFactors (H i) (fun k t => a k t α) (fun k => b k j β),
      mixFactors (H i) (fun l t => c l t β) (fun l => d l j α)]
  simp_rw [← Finset.sum_add_distrib, ← mul_add, h, ← mul_assoc, ← Finset.sum_mul]
  have hHG : H * (u : Matrix X X ℤ) = 1 := Units.inv_mul u
  exact congrArg (fun v : ℤ => v * (if α = β then 1 else 0))
    (by simpa only [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hHG i) j)

/-- Integral coefficients of a tensor flattened on one crossing cut. -/
def crossingMatrix {X Y K : Type*} [Fintype K] (a b : K → X → Y → ℤ) :
    Matrix (X × Y) (X × Y) ℤ :=
  Matrix.of fun i j => ∑ k, a k i.1 i.2 * b k j.1 j.2

/-- Reducing the chosen integral flattening to any field preserves its bound
by the number of intermediate coordinates, including in characteristic two. -/
theorem crossingMatrix_rank_cast {X Y K : Type*} [Fintype X] [Fintype Y] [Fintype K]
    (a b : K → X → Y → ℤ) (F : Type*) [Field F] :
    ((crossingMatrix a b).map (Int.castRingHom F)).rank ≤ Fintype.card K := by
  let A : Matrix (X × Y) K F := Matrix.of fun i k => (a k i.1 i.2 : F)
  let B : Matrix K (X × Y) F := Matrix.of fun k j => (b k j.1 j.2 : F)
  have h : (crossingMatrix a b).map (Int.castRingHom F) = A * B := by
    ext i j
    simp [crossingMatrix, A, B, Matrix.mul_apply]
  exact h ▸ (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width

/-- Both flattenings and their two different bounds specialize simultaneously.
The swapped second coordinates display the opposite cut of the second summand. -/
theorem crossingRanks_overField {X Y K L : Type*} [Fintype X] [Fintype Y]
    [Fintype K] [Fintype L] [DecidableEq X] [DecidableEq Y]
    (a b : K → X → Y → ℤ) (c d : L → X → Y → ℤ)
    (h : ∀ i j α β, ∑ k, a k i α * b k j β + ∑ l, c l i β * d l j α
      = (if i = j then 1 else 0) * (if α = β then 1 else 0)) (F : Type*) [Field F] :
    let P := (crossingMatrix a b).map (Int.castRingHom F)
    let Q := (crossingMatrix c d).map (Int.castRingHom F)
    (∀ i j α β, P (i, α) (j, β) + Q (i, β) (j, α) =
      (if i = j then 1 else 0) * (if α = β then 1 else 0)) ∧
      P.rank ≤ Fintype.card K ∧ Q.rank ≤ Fintype.card L := by
  refine ⟨?_, crossingMatrix_rank_cast a b F, crossingMatrix_rank_cast c d F⟩
  intro i j α β
  simpa only [crossingMatrix, Matrix.map_apply, Matrix.of_apply, map_add, map_mul,
    apply_ite (Int.castRingHom F), map_one, map_zero] using
    congrArg (Int.castRingHom F) (h i j α β)

end Crossing

end VPVNP
end Computability
end OAI
