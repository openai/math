import OAI.LinearAlgebra.FiniteFourier.BatchedPairing
import OAI.LinearAlgebra.FiniteFourier.PhaseTensorValue

/-! # Detecting the two Fourier phases in the paired lists -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical Matrix Kronecker NNReal

variable {K : Type*} [Field K] {R C : Type} [Fintype R] [Fintype C]
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop))

private def legs {F : Fin 4 → Sort*} (a : F 0) (b : F 1) (c : F 2) (d : F 3) : ∀ i, F i :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun i => i.elim0))))

private theorem diagonal_coeff [DecidableEq R] (x : Fin 4 → R) :
    (Raw.diagonal (Fin 4) K R).coeff x =
      if x 0 = x 2 ∧ x 1 = x 3 then (1 : Matrix R R K) (x 0) (x 1) else 0 := by
  have he (r : R) : x = (fun _ => r) ↔ x 0 = r ∧ x 1 = r ∧ x 2 = r ∧ x 3 = r := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨h₀,h₁,h₂,h₃⟩
      funext i
      fin_cases i <;> assumption
  simp only [Raw.diagonal, he, Matrix.one_apply]
  rw [Finset.sum_eq_single (x 0)]
  · split_ifs <;> grind
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem phasePointValue_identity (R : Type) [Fintype R] [DecidableEq R] :
    phasePointValue ψ (1 : Matrix R R K) = Fintype.card R := by
  let e := legs (F := fun i => phaseLeg R R i ≃ R)
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
  have he : ofRaw (phaseRaw (1 : Matrix R R K)) = ofRaw (Raw.diagonal (Fin 4) K R) := by
    apply ofRaw_eq_iff.mpr (Raw.reindex_equivalent e ?_)
    intro z
    refine (phaseRaw_coeff (1 : Matrix R R K) z).trans ?_
    refine Eq.trans ?_ (diagonal_coeff (K := K) (fun i => e i (z i))).symm
    unfold phaseEntry
    congr 1
  rw [phasePointValue, he, ofRaw_diagonal_eq_natCast,
    show ψ.val (Fintype.card R : TensorClass (Fin 4) K) = Fintype.card R from
      map_natCast (normalizedSpectrum.toRingHom ψ) _, NNReal.coe_natCast]

omit [Fintype C] in
private theorem row_supported_sum (M : Matrix R C K) (f : R → C)
    (hf : ∀ i j, j ≠ f i → M i j = 0) (a b : R) (c d : C) :
    phaseEntry M a c b d = ∑ r, (if a = r then M r (f r) else 0) *
      (if c = f r then 1 else 0) * (if b = r then 1 else 0) * (if d = f r then 1 else 0) := by
  rw [Finset.sum_eq_single a]
  · by_cases hc : c = f a
    · subst c
      simp [phaseEntry, eq_comm]
      split_ifs <;> grind
    · simp [phaseEntry, hc, hf a c hc]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem phasePointValue_le_of_row_supported (M : Matrix R C K) (f : R → C)
    (hf : ∀ i j, j ≠ f i → M i j = 0) : phasePointValue ψ M ≤ Fintype.card R := by
  have hr : (phaseRaw M).Restricts (Raw.diagonal (Fin 4) K R) := by
    let term (r : R) (_ : Fin 4) := r
    have hd : (Raw.diagonal (Fin 4) K R).coeff =
        Crossing.basisTensor (A := fun _ : Fin 4 => R) term := by
      funext x
      simp only [Raw.diagonal, Crossing.basisTensor, term]
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> rfl
    change Crossing.IsRestriction (phaseRaw M).coeff (Raw.diagonal (Fin 4) K R).coeff
    rw [hd]
    apply (Crossing.restriction_basisTensor_iff term _).mpr
    let col (c : C) (r : R) : K := if c = f r then 1 else 0
    refine ⟨legs (F := fun i => phaseLeg R C i → R → K)
      (fun a r => if (a : R) = r then M r (f r) else 0) col
      (fun b r => if (b : R) = r then 1 else 0) col, ?_⟩
    intro z
    refine (phaseRaw_coeff M z).trans ?_
    simp only [Fin.prod_univ_four]
    exact row_supported_sum M f hf (z 0) (z 2) (z 1) (z 3)
  have h := ψ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr hr)
  rw [ofRaw_diagonal_eq_natCast, show ψ.val (Fintype.card R : TensorClass (Fin 4) K) =
    Fintype.card R from map_natCast (normalizedSpectrum.toRingHom ψ) _] at h
  simpa [phasePointValue] using NNReal.coe_le_coe.mpr h

theorem phasePointValue_double (H : Matrix R R K) :
    phasePointValue ψ (Matrix.fromBlocks H 0 0 H) = 2 * phasePointValue ψ H := by
  let e := (Equiv.boolProdEquivSum R).symm
  have he : Matrix.fromBlocks H 0 0 H = (Matrix.kronecker (1 : Matrix Bool Bool K) H).submatrix e e := by
    ext i j
    cases i <;> cases j <;> simp [e, Equiv.boolProdEquivSum, Matrix.kronecker]
  rw [he, phasePointValue_submatrix, phasePointValue_kronecker, phasePointValue_identity]
  simp

theorem paired_augmented_phase_bound [DecidableEq R] (H : Matrix R R K)
    (hs : Hᵀ = H) (f : R → R) (hf : ∀ i j, j ≠ f i → (Hᵀ * H) i j = 0) :
    2 * phasePointValue ψ H ≤ phasePointValue ψ ((Matrix.fromCols (1 : Matrix R R K) H)ᵀ *
      Matrix.fromCols H (1 : Matrix R R K)) +
      2 * Fintype.card R := by
  let G := (Matrix.fromCols (1 : Matrix R R K) H)ᵀ * Matrix.fromCols H (1 : Matrix R R K)
  let E := Matrix.fromBlocks H 0 0 H - G
  let p : R ⊕ R → R ⊕ R := Sum.elim Sum.inr (fun i => Sum.inl (f i))
  have hg : G = Matrix.fromBlocks H 1 (Hᵀ * H) H := by
    simp [G, Matrix.transpose_fromCols, hs]
  have he : ∀ i j, j ≠ p i → E i j = 0 := by
    intro i j h
    cases i <;> cases j <;> simp [p] at h <;> simp [E, hg]
    · rw [Matrix.one_apply, ite_eq_right (Ne.symm h)]
    · exact hf _ _ h
  have hb := phasePointValue_le_of_row_supported ψ E p he
  have ha := phasePointValue_add_le ψ G E
  rw [show G + E = Matrix.fromBlocks H 0 0 H from add_sub_cancel ..,
    phasePointValue_double] at ha
  apply ha.trans
  apply add_le_add le_rfl
  simpa [two_mul] using hb

end FiniteFourier
end LinearAlgebra
end OAI
