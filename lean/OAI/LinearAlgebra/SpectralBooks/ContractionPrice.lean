import OAI.LinearAlgebra.SpectralBooks.ConcreteSpectrum
import OAI.LinearAlgebra.SpectralBooks.ClassComparison
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.RawLogPrice

/-!
# Old tensor prices after contracting a new party

A covector on the extra party contracts an enlarged tensor to the old sites.
Taking the supremum of the old prices over all covectors gives a monotone
cost on restriction classes, including for covectors on grouped wire copies.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators NNReal Classical
noncomputable section

namespace SiteTensor

universe v
variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]

namespace Raw

/-- Contract the party indexed by `none` against a covector. -/
def contractNew (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) : Raw.{v} I K where
  Leg i := T.Leg (some i)
  finiteLeg _ := inferInstance
  coeff a := ∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))

omit [Nonempty I] in
/-- A restriction on the enlarged site set pulls the new covector back by the
transpose of the new site's local map. The old sites keep their local maps. -/
theorem contractNew_restricts {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y)
    (ξ : X.Leg none → K) : ∃ η : Y.Leg none → K, (X.contractNew ξ).Restricts (Y.contractNew η) := by
  classical
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hm⟩ := h
  let η (b : Y.Leg none) := ∑ c, ξ c * M none c b
  refine ⟨η, fun i ↦ M (some i), ?_⟩
  intro (x : ∀ i, X.Leg (some i))
  change (∑ c, ξ c * X.coeff (Equiv.piOptionEquivProd.symm (c,x))) =
    ∑ a, (∑ b, η b * Y.coeff (Equiv.piOptionEquivProd.symm (b,a))) * _
  have he (c : X.Leg none) (x : ∀ i, X.Leg (some i)) :
      X.coeff (Equiv.piOptionEquivProd.symm (c,x)) =
        ∑ b, ∑ a, Y.coeff (Equiv.piOptionEquivProd.symm (b,a)) *
          (M none c b * ∏ i, M (some i) (x i) (a i)) := by
    rw [hm, ← Fintype.sum_prod_type']
    apply Fintype.sum_equiv (Equiv.piOptionEquivProd (β := Y.Leg))
    intro y
    rw [Equiv.symm_apply_apply, Fintype.prod_option]
    rfl
  simp_rw [he]
  simp only [η, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ ?_
  dsimp [Equiv.piOptionEquivProd]
  ring

end Raw

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- The old log price of the most expensive contraction, as a supremum. -/
def contractionPrice (T : Raw.{v} (Option I) K) : ℝ :=
  ⨆ ξ : T.Leg none → K, rawLogPrice φ 1 (T.contractNew ξ)

private theorem contraction_bdd (T : Raw.{v} (Option I) K) :
    BddAbove (Set.range fun ξ : T.Leg none → K ↦ rawLogPrice φ 1 (T.contractNew ξ)) := by
  classical
  let d := Fintype.card (∀ i, T.Leg (some i))
  refine ⟨rawLogPrice φ 1 (Raw.diagonal I K (ULift.{v} (Fin d))), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  exact rawLogPrice_mono φ zero_le_one ((T.contractNew ξ).restricts_diagonal I)

theorem le_contractionPrice (T : Raw.{v} (Option I) K) (ξ : T.Leg none → K) :
    rawLogPrice φ 1 (T.contractNew ξ) ≤ contractionPrice φ T := le_ciSup (contraction_bdd φ T) ξ

theorem contractionPrice_mono {X Y : Raw.{v} (Option I) K} (h : X.Restricts Y) :
    contractionPrice φ X ≤ contractionPrice φ Y := by
  apply ciSup_le
  intro ξ
  obtain ⟨η, hη⟩ := Raw.contractNew_restricts h ξ
  exact (rawLogPrice_mono φ zero_le_one hη).trans (le_contractionPrice φ Y η)

theorem contractionPrice_nonneg (T : Raw.{v} (Option I) K) : 0 ≤ contractionPrice φ T :=
  (rawLogPrice_nonneg φ zero_le_one _).trans (le_contractionPrice φ T 0)

omit [Fintype I] [Nonempty I] in
@[simp] theorem contractNew_coeff_sum {T : Raw.{v} (Option I) K} {L : ℕ}
    (ξ : T.Leg none → K) (Z : Fin L → (∀ i, T.Leg i) → K)
    (hs : T.coeff = ∑ l, Z l) :
    (T.contractNew ξ).coeff = ∑ l, (({T with coeff := Z l} : Raw _ K).contractNew ξ).coeff := by
  funext (a : ∀ i, T.Leg (some i))
  change (∑ b, ξ b * T.coeff (Equiv.piOptionEquivProd.symm (b,a))) = _
  simp only [hs, Finset.sum_apply, Finset.mul_sum, Raw.contractNew]
  rw [Finset.sum_comm]
  exact (Finset.sum_apply a Finset.univ (fun l : Fin L ↦ fun y : (∀ i, T.Leg (some i)) ↦ ∑ b, ξ b * Z l (Equiv.piOptionEquivProd.symm (b,y)))).symm

/-- The contraction estimate is independent of the tensor representative. -/
def classContractionPrice (X : TensorClass.{v} (Option I) K) : ℝ :=
  Quotient.liftOn X (contractionPrice φ) fun _ _ h ↦
    le_antisymm (contractionPrice_mono φ h.1) (contractionPrice_mono φ h.2)

theorem classContractionPrice_mono {X Y : TensorClass.{v} (Option I) K} (h : X ≤ Y) :
    classContractionPrice φ X ≤ classContractionPrice φ Y := by
  induction X, Y using Quotient.inductionOn₂ with | _ X Y =>
    exact contractionPrice_mono φ h

/-- One already-chosen summand realizes the largest contraction supremum.
Every covector bounds the price of the contracted sum by that supremum and
the cost of the summand tag, so the same holds after maximizing in the covector. -/
theorem classContractionPrice_ordinary_sum
    (X : NonzeroProduct.{v} (Option I) K) (L : ℕ) (Z : Fin L → NonzeroProduct.{v} (Option I) K)
    (h : ClassOrdinarySum X L Z) :
    ∃ l, classContractionPrice φ (classOfProduct X) ≤
      classContractionPrice φ (classOfProduct (Z l)) + Real.logb 2 L := by
  classical
  obtain ⟨T, z, hT, hsum, hz⟩ := h
  have hL : 0 < L := by
    by_contra! hL
    obtain rfl : L = 0 := Nat.eq_zero_of_le_zero hL
    exact X.toMul.property (hT.symm.trans ((ofRaw_eq_zero_iff T).mpr (by simpa using hsum)))
  have : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l ↦ classContractionPrice φ (classOfProduct (Z l)))
  refine ⟨j, ?_⟩
  rw [← hT]
  change contractionPrice φ T ≤ _
  apply ciSup_le
  intro ξ
  have hh := contractNew_coeff_sum ξ z hsum
  by_cases he : (T.contractNew ξ).coeff = 0
  · rw [rawLogPrice_zero φ 1 _ he, ← hz j]
    exact add_nonneg (contractionPrice_nonneg φ _) (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast hL : (1 : ℝ) ≤ L))
  let zz (l : Fin L) := ({T with coeff := z l} : Raw _ K).contractNew ξ
  let C (l : Fin L) : (∀ i, T.Leg (some i)) → K := (zz l).coeff
  change (T.contractNew ξ).coeff = ∑ l, C l at hh
  obtain ⟨l, _, hp⟩ := ordinary_sum_logb_le φ C (hh ▸ he) zero_le_one
  have hprice : rawLogPrice φ 1 (T.contractNew ξ) ≤ rawLogPrice φ 1 (zz l) + Real.logb 2 L := by
    have heq := congrArg (coeffValue φ (A := fun i => T.Leg (some i))) hh
    simp only [← heq, Fintype.card_fin, one_mul] at hp
    simpa [rawLogPrice, coeffValue, ofCoeffs, C, zz, Raw.contractNew] using hp
  refine hprice.trans (add_le_add_left (?_ : rawLogPrice φ 1 (zz l) ≤ _) _)
  exact (le_contractionPrice φ {T with coeff := z l} ξ).trans (by
    change classContractionPrice φ (ofRaw _) ≤ _
    rw [hz]
    exact hj l)

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
