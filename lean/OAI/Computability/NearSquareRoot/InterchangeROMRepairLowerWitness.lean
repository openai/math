import OAI.Computability.NearSquareRoot.InterchangeROMRepair
import OAI.Computability.NearSquareRoot.InterchangeROMRepairLower
import OAI.Computability.NearSquareRoot.InterchangeROMRepairFinite
import OAI.Computability.NearSquareRoot.InterchangeSpectralComponents

/-! # A witness for the executable binary pencil certificate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace InterchangeROMRepair.Lower

open OAI.LinearAlgebra.FiniteFourier Matrix SwapRepair

variable {K : Type} [Field K] {m : ℕ}

abbrev RowIndex (m : ℕ) := Fin (width m) × BasisIndex m
abbrev CheckIndex (m : ℕ) := Fin (checks m) × BasisIndex m

/-- Store both pencil terms and both Hermite check directions in base-field coordinates. -/
def frozen (e : Environment K m) (T : Table K m) : Spec K (RowIndex m) (CheckIndex m) m where
  base := mixerMatrix e.pencil.A₀
  term j := mixerMatrix (fun β => e.pencil.A β j 1)
  extract := flattenMatrix (repairCheck e.nodes (checks m))
  restore := flattenMatrix (repairCheck e.nodes (checks m))ᵀ
  correct η := tableMatrix T (signPattern η)

theorem frozen_pow_mulVec (e : Environment K m) (T : Table K m) (η : Fin m → Bool)
    (x : Fin (width m) → Coeff K m) :
    onSign (frozen e T) η ^ order m *ᵥ flatten x = flatten (predictor e η * x) := by
  change (mixerMatrix e.pencil.A₀ + ∑ j, (if η j then (-1 : K) else 1) •
    mixerMatrix (fun β => e.pencil.A β j 1)) ^ order m *ᵥ flatten x = _
  rw [signed_eq, evaluated_pow_mulVec]

/-- Every candidate auxiliary table gives exactly its mathematical scalar transfer,
including candidates that do not implement a correct repair. -/
theorem frozen_runSign (e : Environment K m) (T : Table K m) (η : Fin m → Bool)
    (half : K) (hh : 2 * half = 1) (x : Fin (width m) → Coeff K m) :
    runSign (frozen e T) η (order m) half (flatten x) =
      flatten (ROMCheck.scalar e T (signPattern η) x) := by
  have inv := InterchangeSpectralComponents.invRadix_eq e half hh
  let H := repairCheck e.nodes (checks m)
  let k := signPattern η
  let p := predictor e η
  have hext (x : Fin (width m) → Coeff K m) : (frozen e T).extract *ᵥ flatten x = flatten (H *ᵥ x) :=
    flattenMatrix_mulVec _ _
  have hrest (y : Fin (checks m) → Coeff K m) : (frozen e T).restore *ᵥ flatten y = flatten (Hᵀ *ᵥ y) :=
    flattenMatrix_mulVec _ _
  have hcorr (b : Bool) (x y : Fin (checks m) → Coeff K m) :
      (frozen e T).correct η b false *ᵥ flatten x + (frozen e T).correct η b true *ᵥ flatten y =
        flatten (if b then (T k (x,y)).2 else (T k (x,y)).1) :=
    tableMatrix_mulVec T k b x y
  simp only [runSign,frozen_pow_mulVec,hext,hrest,hcorr,Bool.false_eq_true,ite_false,ite_true,
    ← flatten_sub,← flatten_smul,← flatten_add]
  apply congrArg flatten
  funext i
  change p i * x i - half • (p i * (p i * (p i * x i)) - p i * x i) -
    p i * (Hᵀ *ᵥ (T k (H *ᵥ (p*x),H *ᵥ x)).1) i +
    (Hᵀ *ᵥ (T k (H *ᵥ (p*x),H *ᵥ x)).2) i =
    (p i - e.invRadix * (p i ^ 3 - p i)) * x i -
    p i * (Hᵀ *ᵥ (T k (H *ᵥ (p*x),H *ᵥ x)).1) i +
    (Hᵀ *ᵥ (T k (H *ᵥ (p*x),H *ᵥ x)).2) i
  rw [Algebra.smul_def,inv]
  ring

theorem queryProduct_eq (e : Environment K m) (η : Fin m → Bool) :
    countQueryProduct e.root (signPattern η) = algebraMap K (Coeff K m) (signProduct η : K) := by
  rw [countQueryProduct,signProduct,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases h : η j <;> simp [digitPhase_apply,signPattern,h,charSign,ZMod.val_one_eq_one_mod]

/-- Freezing an arbitrary table preserves the complete finite test against physical repair. -/
theorem accepts_of_scalar [DecidableEq K] (e : Environment K m) (T : Table K m)
    (h : ROMCheck.ScalarCorrect e T) (half : K) (hh : 2 * half = 1) :
    accepts (frozen e T) (order m) half = true := by
  rw [accepts_iff_rows]
  intro η y
  obtain ⟨x,rfl⟩ := (flatEquiv K (Fin (width m)) m).surjective y
  change runSign _ _ _ _ (flatten x) = _ • flatten x
  rw [frozen_runSign _ _ _ _ hh,← flatten_smul]
  apply congrArg flatten
  funext i
  rw [h,queryProduct_eq e η]
  rw [Pi.smul_apply,Algebra.smul_def]

theorem signPattern_surjective (m : ℕ) : Function.Surjective (signPattern (m := m)) := by
  intro k
  refine ⟨fun j => decide (k j ≠ 0),?_⟩
  funext j
  have binary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases binary (k j) with h | h <;> simp [signPattern,h]

theorem accepts_iff_scalar [DecidableEq K] (e : Environment K m) (T : Table K m)
    (half : K) (hh : 2 * half = 1) :
    accepts (frozen e T) (order m) half = true ↔ ROMCheck.ScalarCorrect e T := by
  refine ⟨?_,fun h => accepts_of_scalar e T h half hh⟩
  intro h k x i
  obtain ⟨η,rfl⟩ := signPattern_surjective m k
  have h' := (accepts_iff_rows _ _ _).mp h η (flatten x)
  rw [frozen_runSign _ _ _ _ hh,← flatten_smul] at h'
  have v := (flatEquiv K (Fin (width m)) m).injective h'
  rw [queryProduct_eq e η]
  simpa only [Pi.smul_apply,Algebra.smul_def] using congrFun v i

theorem accepts_iff_binary [DecidableEq K] (e : Environment K m) (T : Table K m)
    (half : K) (hh : 2 * half = 1) :
    accepts (frozen e T) (order m) half = true ↔ ROMCheck.CorrectOn e T (Fin 2) :=
  (accepts_iff_scalar e T half hh).trans (ROMCheck.correct_iff_scalar e T).symm

/-- The executable finite matrix search has a witness with the prescribed dimensions
and pencil order, for every odd-characteristic ground field and every legal parameter. -/
theorem exists_accepted [DecidableEq K] (hm : 2 ≤ m) (half : K) (hh : 2 * half = 1) :
    ∃ t : Spec K (RowIndex m) (CheckIndex m) m, accepts t (order m) half = true := by
  obtain ⟨e⟩ := exists_environment K (isUnit_iff_exists_inv.mpr ⟨half,hh⟩) m
  obtain ⟨T,hT⟩ := exists_table hm e
  exact ⟨frozen e T,accepts_of_scalar e T (ROMCheck.scalar_of_binary e T (hT (Fin 2))) _ hh⟩

end InterchangeROMRepair.Lower

end

end NearSquareRoot
end Computability
end OAI
