import OAI.LinearAlgebra.SpectralBooks.ContractNonzero
import OAI.LinearAlgebra.SpectralBooks.ContractSum

/-! # Contraction prices of repeated tensors

In a block direct sum, a covector is a pair of independent covectors on its
summands. Thus the supremum of the ordinary spectral values is additive.
Taking logarithms gives the exact price increase for a positive number of
copies of a nonzero tensor.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Classical

noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

private def contractedValue (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) : ℝ :=
  φ.val (ofRaw (T.contractNew ξ))

private def rawContractionValue (T : Raw.{v} (Option I) K) : ℝ :=
  ⨆ ξ, contractedValue φ T ξ

private theorem rawContractionValue_bdd (T : Raw.{v} (Option I) K) :
    BddAbove (Set.range (contractedValue φ T)) := by
  let d := Fintype.card (∀ i, T.Leg (some i))
  refine ⟨(φ.val (ofRaw (Raw.diagonal I K (ULift.{v} (Fin d)))) : ℝ), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact_mod_cast φ.property.2.2.2.2 _ _ (ofRaw_le_iff.mpr ((T.contractNew ξ).restricts_diagonal I))

private theorem le_rawContractionValue (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) :
    contractedValue φ T ξ ≤ rawContractionValue φ T :=
  le_ciSup (rawContractionValue_bdd φ T) ξ

private theorem rawContractionValue_mono {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y) :
    rawContractionValue φ X ≤ rawContractionValue φ Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := Raw.contractNew_restricts h ξ
  apply le_trans _ (le_rawContractionValue φ Y η)
  exact_mod_cast φ.property.2.2.2.2 _ _ (ofRaw_le_iff.mpr hη)

/-- The supremum of the ordinary values of all contractions at the extra site. -/
def classContractionValue (X : TensorClass.{v} (Option I) K) : ℝ :=
  Quotient.liftOn X (rawContractionValue φ) fun _ _ h ↦
    le_antisymm (rawContractionValue_mono φ h.1) (rawContractionValue_mono φ h.2)

theorem classContractionPrice_eq_logb {X : TensorClass.{v} (Option I) K}
    (h : 1 ≤ classContractionValue φ X) :
    classContractionPrice φ X = Real.logb 2 (classContractionValue φ X) := by
  induction X using Quotient.inductionOn with | _ T =>
    change 1 ≤ rawContractionValue φ T at h
    change contractionPrice φ T = Real.logb 2 (rawContractionValue φ T)
    apply le_antisymm
    · apply ciSup_le
      intro ξ
      change 1 * Real.logb 2 (contractedValue φ T ξ) ≤ _
      rw [one_mul]
      by_cases hz : contractedValue φ T ξ = 0
      · simpa [hz] using Real.logb_nonneg (b := 2) (by norm_num) h
      · have hp : 0 ≤ contractedValue φ T ξ := NNReal.coe_nonneg _
        exact Real.logb_le_logb_of_le (by norm_num) (lt_of_le_of_ne hp (Ne.symm hz))
          (le_rawContractionValue φ T ξ)
    · apply (Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le h)).mpr
      apply ciSup_le
      intro ξ
      by_cases hz : contractedValue φ T ξ = 0
      · rw [hz]
        positivity
      · have hp : 0 ≤ contractedValue φ T ξ := NNReal.coe_nonneg _
        apply (Real.logb_le_iff_le_rpow (by norm_num) (lt_of_le_of_ne hp (Ne.symm hz))).mp
        simpa only [rawLogPrice, one_mul, contractedValue] using le_contractionPrice φ T ξ

theorem one_le_classContractionValue {X : TensorClass.{v} (Option I) K} (hX : X ≠ 0) :
    1 ≤ classContractionValue φ X := by
  induction X using Quotient.inductionOn with | _ T =>
    obtain ⟨ξ, hξ⟩ := T.exists_contractNew_ne_zero (fun h ↦ hX ((ofRaw_eq_zero_iff T).mpr h))
    apply le_trans _ (le_rawContractionValue φ T ξ)
    exact_mod_cast one_le_raw_spectralValue φ (T.contractNew ξ) hξ

/-- The old spectral values of the blocks add, and their covectors can be
chosen independently. -/
theorem classContractionValue_add (X Y : TensorClass.{v} (Option I) K) :
    classContractionValue φ (X + Y) = classContractionValue φ X + classContractionValue φ Y := by
  induction X, Y using Quotient.inductionOn₂ with | _ X Y =>
    change rawContractionValue φ (X.add Y) = rawContractionValue φ X + rawContractionValue φ Y
    have hv (ζ : X.Leg none ⊕ Y.Leg none → K) :
        contractedValue φ (X.add Y) ζ =
          contractedValue φ X (ζ ∘ Sum.inl) + contractedValue φ Y (ζ ∘ Sum.inr) := by
      simp only [contractedValue, ofRaw_contractNew_add, φ.property.2.2.1, NNReal.coe_add]
    apply le_antisymm
    · apply ciSup_le
      intro ζ
      apply (hv ζ).le.trans
      exact add_le_add (le_rawContractionValue φ X _) (le_rawContractionValue φ Y _)
    · apply le_sub_iff_add_le.mp
      apply ciSup_le
      intro ξ
      apply le_sub_iff_add_le.mpr
      apply le_sub_iff_add_le'.mp
      apply ciSup_le
      intro η
      apply le_sub_iff_add_le'.mpr
      exact (hv (Sum.elim ξ η)).symm.le.trans (le_rawContractionValue φ (X.add Y) _)

theorem classContractionValue_natCast_mul (k : ℕ) (X : TensorClass.{v} (Option I) K) :
    classContractionValue φ (k * X) = k * classContractionValue φ X := by
  induction k with
  | zero =>
    have h := classContractionValue_add φ (0 : TensorClass.{v} (Option I) K) 0
    simp only [add_zero] at h
    simpa using (show classContractionValue φ (0 : TensorClass.{v} (Option I) K) = 0 by linarith)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, classContractionValue_add, ih,
      Nat.cast_succ, add_mul, one_mul]

/-- A positive full diagonal at all sites raises the contraction price of a
nonzero enlarged tensor by the logarithm of its number of labels. -/
theorem classContractionPrice_natCast_mul {k : ℕ} (hk : 0 < k)
    {X : TensorClass.{v} (Option I) K} (hX : X ≠ 0) :
    classContractionPrice φ (k * X) = Real.logb 2 k + classContractionPrice φ X := by
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hval := one_le_classContractionValue φ hX
  have hmul : 1 ≤ classContractionValue φ (k * X) := by
    rw [classContractionValue_natCast_mul]
    exact one_le_mul_of_one_le_of_one_le hk' hval
  rw [classContractionPrice_eq_logb φ hmul, classContractionPrice_eq_logb φ hval,
    classContractionValue_natCast_mul, Real.logb_mul (by positivity) (zero_lt_one.trans_le hval).ne']

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
