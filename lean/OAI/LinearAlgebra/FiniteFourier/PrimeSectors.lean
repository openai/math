import OAI.LinearAlgebra.FiniteFourier.PrimeDigits
import OAI.LinearAlgebra.FiniteFourier.CircuitParallel
import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # Ternary Fourier sectors of a four-coordinate tensor stage -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

variable {K : Type*} [CommRing K] {j : ℕ}

/-- One ternary Fourier transform and one fixed coordinate. -/
def ternarySectorStage (ζ : K) : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) K :=
  Matrix.fromBlocks (dftMatrix 3 ζ) 0 0 1

private def sectorWord (S : Finset (Fin j)) (x : S → Fin 3) (i : Fin j) : Fin 3 ⊕ Unit :=
  if h : i ∈ S then Sum.inl (x ⟨i, h⟩) else Sum.inr ()

/-- A four-coordinate word is determined by the positions of its active
ternary digits and their values. -/
private def sectorEquiv (j : ℕ) :
    (Σ S : Finset (Fin j), S → Fin 3) ≃ (Fin j → Fin 3 ⊕ Unit) :=
  Equiv.ofBijective (fun p i => sectorWord p.1 p.2 i) <| by
    constructor
    · rintro ⟨S, x⟩ ⟨T, y⟩ h
      have heq (i : Fin j) : sectorWord S x i = sectorWord T y i := congrFun h i
      have hST : S = T := by
        ext i
        have hi := congrArg Sum.isLeft (heq i)
        by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;> simp_all [sectorWord]
      subst T
      have hxy : x = y := by
        funext i
        simpa [sectorWord, i.property] using heq i
      rw [hxy]
    · intro w
      let S := Finset.univ.filter (fun i => (w i).isLeft)
      refine ⟨⟨S, fun i => Sum.elim id (fun _ => 0) (w i)⟩, ?_⟩
      funext i
      change sectorWord S _ i = _
      cases he : w i with
      | inl u => simp [S, sectorWord, he]
      | inr u => cases u; simp [S, sectorWord, he]

private def sectorMatrix (ζ : K) (S : Finset (Fin j)) : Matrix (S → Fin 3) (S → Fin 3) K :=
  fun x y => ∏ i, dftMatrix 3 ζ (x i) (y i)

private theorem sectorMatrix_cost (ζ : K) (S : Finset (Fin j)) :
    RealizableAtMost (sectorMatrix ζ S) (complexity (primeTransform 3 S.card ζ)) := by
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  let f := e.symm.arrowCongr (Equiv.refl (Fin 3))
  have h := (realizableAtMost_complexity (primeTransform 3 S.card ζ)).reindex f f
  convert h using 1
  ext x y
  exact Fintype.prod_equiv e _ _ (fun i => by simp [f, dftMatrix])

private theorem sectorMatrix_block (ζ : K) (j : ℕ) :
    (gridTensor (fun _ : Fin j => ternarySectorStage ζ)).submatrix (sectorEquiv j) (sectorEquiv j) =
      Matrix.blockDiagonal' (sectorMatrix (j := j) ζ) := by
  classical
  ext ⟨S, x⟩ ⟨T, y⟩
  by_cases he : S = T
  · subst T
    rw [Matrix.blockDiagonal'_apply_eq]
    change (∏ i, ternarySectorStage ζ (sectorWord S x i) (sectorWord S y i)) = _
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
    have hOne : (∏ i : {i : Fin j // i ∉ S},
        ternarySectorStage ζ (sectorWord S x i) (sectorWord S y i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [sectorWord, i.2, ternarySectorStage, Matrix.fromBlocks]
    rw [hOne, mul_one]
    unfold sectorMatrix
    apply Finset.prod_congr
    · ext i
      simp
    · intro i _
      simp [sectorWord, i.2, ternarySectorStage, Matrix.fromBlocks]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ he]
    change (∏ i, ternarySectorStage ζ (sectorWord S x i) (sectorWord T y i)) = 0
    have hdiff : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      exact not_forall.mp (fun h => he (Finset.ext h))
    obtain ⟨i, hi⟩ := hdiff
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp_all [sectorWord, ternarySectorStage, Matrix.fromBlocks]

/-- Each subset of active positions contributes one ternary Fourier circuit on
exactly that many digits. -/
theorem complexity_ternarySectorStage (ζ : K) (j : ℕ) :
    complexity (gridTensor (fun _ : Fin j => ternarySectorStage ζ)) ≤
      ∑ S : Finset (Fin j), complexity (primeTransform 3 S.card ζ) := by
  let e := sectorEquiv j
  have h := RealizableAtMost.blockDiagonal' (fun S => sectorMatrix_cost (j := j) ζ S)
  rw [← sectorMatrix_block] at h
  simpa [e, Matrix.submatrix_submatrix] using
    (complexity_le_iff _ _).mpr (h.submatrix e.symm e.symm.toEmbedding)

/-- Summing the point counts of the ternary sectors gives the full four-letter volume. -/
theorem sum_ternary_sector_volume (j : ℕ) : ∑ S : Finset (Fin j), 3 ^ S.card = 4 ^ j := by
  simpa [Fintype.card_sigma] using Fintype.card_congr (sectorEquiv j)

/-- A uniform per-entry bound on ternary transforms holds on the four-letter stage. -/
theorem ternarySectorStage_bound (ζ : K) (j : ℕ) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (hc : ∀ k ≤ j, (complexity (primeTransform 3 k ζ) : ℝ) ≤ C * 3^k * (1 + (k : ℝ))^β) :
    (complexity (gridTensor (fun _ : Fin j => ternarySectorStage ζ)) : ℝ) ≤
      C * 4^j * (1 + (j : ℝ))^β := by
  have hvol : ∑ S : Finset (Fin j), (3 : ℝ)^S.card = (4 : ℝ)^j := by
    exact_mod_cast sum_ternary_sector_volume j
  calc
    _ ≤ ∑ S : Finset (Fin j), (complexity (primeTransform 3 S.card ζ) : ℝ) := by
      exact_mod_cast complexity_ternarySectorStage ζ j
    _ ≤ ∑ S : Finset (Fin j), C * 3 ^ S.card * (1 + (j : ℝ))^β := by
      apply Finset.sum_le_sum
      intro S _
      have hSj : S.card ≤ j := by simpa using S.card_le_univ
      refine (hc S.card hSj).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_left hSj 1) hβ
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, hvol]

end

end FiniteFourier
end LinearAlgebra
end OAI
