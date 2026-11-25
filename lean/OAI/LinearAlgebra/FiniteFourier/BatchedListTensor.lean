import OAI.LinearAlgebra.FiniteFourier.BatchedGram
import OAI.LinearAlgebra.FiniteFourier.PhaseSublevels
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.SpectralDiagonal

/-! # Spectral tests on the doubled list

The two column-index legs are distinct tensor sites with the same label. Pairing
the vector legs of two lists gives the four-terminal phase tensor of their Gram
matrix. The list value is subadditive, bounded by the number of columns, and has
Zariski-closed sublevels.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical BigOperators Matrix NNReal
noncomputable section

abbrev listLeg (R C : Type) : Fin 3 → Type := ![R,C,C]

private def triple {F : Fin 3 → Sort*} (a : F 0) (b : F 1) (c : F 2) : ∀ i, F i :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun i => i.elim0)))

instance listLegFintype (R C : Type) [Fintype R] [Fintype C] (i : Fin 3) :
    Fintype (listLeg R C i) :=
  triple (F := fun j => Fintype (listLeg R C j)) (inferInstance : Fintype R)
    (inferInstance : Fintype C) (inferInstance : Fintype C) i

variable {K : Type*} [Field K] {R C D : Type} [Fintype R] [Fintype C] [Fintype D]

/-- The list tensor with coefficients of ∑ⱼ uⱼ ⊗ eⱼ ⊗ eⱼ. -/
def listRaw (U : Matrix R C K) : Raw (Fin 3) K where
  Leg := listLeg R C
  finiteLeg := listLegFintype R C
  coeff z := if (z 1 : C) = z 2 then U (z 0) (z 1) else 0

def listCoordinates (r : R) (a b : C) : ∀ i, listLeg R C i :=
  triple r a b

/-- Contracting the vector index is exactly the phase lift of the bilinear pairing. -/
theorem listRaw_pair (U : Matrix R C K) (V : Matrix R D K) (z : ∀ i, phaseLeg C D i) :
    (phaseRaw (Uᵀ * V)).coeff z =
      ∑ r, (listRaw U).coeff (listCoordinates r (z 0 : C) (z 2 : C)) *
        (listRaw V).coeff (listCoordinates r (z 1 : D) (z 3 : D)) := by
  rw [phaseRaw_coeff]
  change (if (z 0 : C) = z 2 ∧ (z 1 : D) = z 3 then (Uᵀ * V) (z 0) (z 1) else 0) =
    ∑ r, (if (z 0 : C) = z 2 then U r (z 0) else 0) *
      (if (z 1 : D) = z 3 then V r (z 1) else 0)
  generalize (z 0 : C) = a, (z 2 : C) = b, (z 1 : D) = c, (z 3 : D) = d
  change C at a b
  change D at c d
  split_ifs with h h' h'' <;> simp_all [Matrix.mul_apply]
  exact (h rfl rfl).elim

private abbrev listCoeffs (U : Matrix R C K) : ((i : Fin 3) → listLeg R C i) → K :=
  (listRaw U).coeff

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop))

/-- Evaluation of the list at a normalized spectral point on its three sites. -/
def listValue (U : Matrix R C K) : ℝ≥0 := φ.val (ofRaw (listRaw U))

theorem listValue_add_le (U V : Matrix R C K) :
    listValue φ (U + V) ≤ listValue φ U + listValue φ V := by
  have hc : listCoeffs (U + V) = listCoeffs U + listCoeffs V := by
    funext z
    change (if (z 1 : C) = z 2 then U (z 0) (z 1) + V (z 0) (z 1) else 0) =
      (if (z 1 : C) = z 2 then U (z 0) (z 1) else 0) +
      (if (z 1 : C) = z 2 then V (z 0) (z 1) else 0)
    generalize (z 1 : C) = c, (z 2 : C) = d
    change C at c d
    split_ifs <;> simp
  have hr : (listRaw (U + V)).Restricts ((listRaw U).add (listRaw V)) := by
    change Crossing.IsRestriction (listCoeffs (U + V)) (sumCoeff (listCoeffs U) (listCoeffs V))
    rw [hc]
    exact ordinary_add_restricts _ _
  simpa only [listValue, ofRaw_add, φ.2.2.2.1] using φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr hr)

omit [Fintype R] in
private theorem column_sum (U : Matrix R C K) (r : R) (a b : C) :
    (if a = b then U r a else 0) =
      ∑ c : C, U r c * (if a = c then 1 else 0) * (if b = c then 1 else 0) := by
  rw [Finset.sum_eq_single b]
  · by_cases h : a = b <;> simp_all
  · intro c _ hc
    simp [hc.symm]
  · simp

omit [Fintype R] in
private theorem supported_column_sum (U : Matrix R C K) (s : Finset C)
    (hs : ∀ r c, c ∉ s → U r c = 0) (r : R) (a b : C) :
    (if a = b then U r a else 0) =
      ∑ c : s, U r c.val * (if a = c.val then 1 else 0) * (if b = c.val then 1 else 0) := by
  let f (c : C) := U r c * (if a = c then 1 else 0) * (if b = c then 1 else 0)
  rw [column_sum]
  exact (Finset.sum_subset (Finset.subset_univ s)
    (f := f) (fun c _ hc => by simp [f, hs r c hc])).symm.trans (Finset.sum_attach s f).symm

/-- Only the labels of nonzero columns have to be supplied to the three legs. -/
theorem listRaw_restricts_supported (U : Matrix R C K) (s : Finset C)
    (hs : ∀ r c, c ∉ s → U r c = 0) :
    (listRaw U).Restricts (Raw.diagonal (Fin 3) K s) := by
  let term (c : s) (_ : Fin 3) := c
  have hd : (Raw.diagonal (Fin 3) K s).coeff =
      Crossing.basisTensor (A := fun _ : Fin 3 => s) term := by
    funext x
    simp only [Raw.diagonal, Crossing.basisTensor, term]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  change Crossing.IsRestriction (listCoeffs U) (Raw.diagonal (Fin 3) K s).coeff
  rw [hd]
  apply (Crossing.restriction_basisTensor_iff term _).mpr
  let eqLabel : C → s → K := fun i j => if i = j.val then 1 else 0
  refine ⟨triple (F := fun j => listLeg R C j → s → K)
    (fun r c => U r c.val) eqLabel eqLabel, ?_⟩
  intro z
  simp only [Fin.prod_univ_three]
  change (if (z 1 : C) = z 2 then U (z 0) (z 1) else 0) =
    ∑ c : s, U (z 0) c.val * (if (z 1 : C) = c.val then 1 else 0) *
      (if (z 2 : C) = c.val then 1 else 0)
  exact supported_column_sum U s hs (z 0) (z 1) (z 2)

/-- Sending the column index to each leg supplies the whole list at cost at most
its number of columns, independently of the number of vector coordinates. -/
theorem listValue_le_columns (U : Matrix R C K) : listValue φ U ≤ Fintype.card C := by
  have hr := listRaw_restricts_supported U Finset.univ (by simp)
  have h := φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr hr)
  rw [ofRaw_diagonal_eq_natCast, Fintype.card_coe, Finset.card_univ,
    show φ.val (Fintype.card C : TensorClass (Fin 3) K) =
    Fintype.card C from map_natCast (normalizedSpectrum.toRingHom φ) _] at h
  exact h

private def listCoordinatesEquiv (R C : Type) : ((i : Fin 3) → listLeg R C i) ≃ R × C × C where
  toFun z := (z 0, z 1, z 2)
  invFun p := listCoordinates p.1 p.2.1 p.2.2
  left_inv z := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

omit [Fintype D] in
private theorem sum_list_project (Q : Matrix D R K) (U : Matrix R C K) (d : D) (a b : C) :
    (if a = b then (Q * U) d a else 0) =
      ∑ r, ∑ i : C, ∑ j : C, (if i = j then U r i else 0) *
        (Q d r * (if a = i then 1 else 0) * (if b = j then 1 else 0)) := by
  by_cases eq : a = b
  · subst b
    simp [Matrix.mul_apply, mul_ite, mul_comm]
  · simp [mul_ite, ite_mul, eq]

theorem listRaw_mul_restricts (Q : Matrix D R K) (U : Matrix R C K) :
    (listRaw (Q * U)).Restricts (listRaw U) := by
  change Crossing.IsRestriction (listCoeffs (Q * U)) (listCoeffs U)
  let eqLabel (i j : C) : K := if i = j then 1 else 0
  refine ⟨triple (F := fun i => listLeg D C i → listLeg R C i → K) Q eqLabel eqLabel, ?_⟩
  intro z
  let : DecidableEq (Fin 3) := Classical.decEq _
  let localMaps := triple (F := fun i => listLeg D C i → listLeg R C i → K) Q eqLabel eqLabel
  let summand (a : ∀ i, listLeg R C i) := listCoeffs U a * ∏ i, localMaps i (z i) (a i)
  apply Eq.trans _ ((listCoordinatesEquiv R C).symm.sum_comp summand)
  simp only [Fintype.sum_prod_type]
  simp only [summand, Fin.prod_univ_three]
  exact sum_list_project Q U (z 0) (z 1) (z 2)

/-- A row quotient acts locally on the vector leg and cannot increase list value. -/
theorem listValue_mul_le (Q : Matrix D R K) (U : Matrix R C K) :
    listValue φ (Q * U) ≤ listValue φ U :=
  φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (listRaw_mul_restricts Q U))

/-- Sublevel sets remain closed when the two label legs are constrained to coincide. -/
theorem listValue_le_of_mem_closure {S : Set (Matrix R C K)} {M : Matrix R C K}
    (h : matrixPoint M ∈ affineZariskiClosure (matrixPoint '' S)) {b : ℝ≥0}
    (hb : ∀ A ∈ S, listValue φ A ≤ b) : listValue φ M ≤ b := by
  let f (z : ∀ i, listLeg R C i) : MvPolynomial (R × C) K :=
    if (z 1 : C) = z 2 then MvPolynomial.X (z 0, z 1) else 0
  have he (A : Matrix R C K) :
      (fun z => MvPolynomial.eval (matrixPoint A) (f z)) = listCoeffs A := by
    funext z
    change MvPolynomial.eval (matrixPoint A) (if (z 1 : C) = z 2 then MvPolynomial.X (z 0, z 1) else 0) =
      (if (z 1 : C) = z 2 then A (z 0) (z 1) else 0)
    generalize (z 1 : C) = a, (z 2 : C) = c
    change C at a c
    split_ifs <;> simp [matrixPoint]
  apply coeffValue_le_of_mem_closure (A := listLeg R C) φ (T := listCoeffs M) (S := listCoeffs '' S)
  · rw [← he M]
    apply mapsTo_affineZariskiClosure_of_polynomial f _ h
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨A, hA, (he A).symm⟩
  · rintro _ ⟨A, hA, rfl⟩
    exact hb A hA

end
end FiniteFourier
end LinearAlgebra
end OAI
