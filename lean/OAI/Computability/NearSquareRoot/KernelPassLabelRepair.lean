import OAI.Computability.NearSquareRoot.KernelPassLabelBank
import OAI.Computability.NearSquareRoot.KernelPassRepairAssembly

/-! # The full-rate binary repair on a jointly routed pencil

A single call to the pencil stage operates on every label. At the repair
boundary each label has its own independent pair of syndrome banks, while
the sharing inside the four predictors is preserved.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Plan

open Matrix PencilSearch PencilCoordinates RepairCoordinates PencilDescent PencilDyadicMix CyclotomicCode

variable {A h m N : ℕ} {L : Type*}

/-- Spectral data of one labelled copy, including every independent rational
basis lane of its power-of-two extension. -/
def labelSlice (e : L ≃ Fin N) (v : L) (y : Addr A h)
    (x : Bank A h (N*basisWidth m)) : Fin (batchWidth m) × Coord (batchExponent m) → ℚ :=
  frequencyRows (groupRows (groupIndex e _) v x) y

/-- Constant extension-valued row mixing, separately on the linear data lanes
of each label. -/
def labelMix {i o a : ℕ} (e : L ≃ Fin N) (M : Matrix (Fin o) (Fin i) (Number a)) :
    Plan A (N*(i*2^a)) (N*(o*2^a)) :=
  localGroups (groupIndex e _) (groupIndex e _) (fun _ => rowMix A (.refl _) (.refl _) M)

@[simp] theorem calls_labelMix {i o a : ℕ} (e : L ≃ Fin N)
    (M : Matrix (Fin o) (Fin i) (Number a)) : (labelMix (A := A) e M).calls = 0 :=
  calls_localGroups _ _ _ (fun _ => rfl)

theorem frequency_labelMix {i o a : ℕ} (e : L ≃ Fin N) (M : Matrix (Fin o) (Fin i) (Number a))
    (v : L) (x : Bank A h (N*(i*2^a))) (y : Addr A h) :
    frequencyRows (groupRows (groupIndex e _) v ((labelMix e M).applyAt h x)) y =
      flattenRat M *ᵥ frequencyRows (groupRows (groupIndex e _) v x) y := by
  rw [labelMix, groupRows_localGroups, frequencyRows_rowMix]

def labelTable {s a : ℕ} (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (T : Signature m → CheckRows a s) : Plan A (N*(s*2^a)+N*(s*2^a)) (N*(s*2^a)+N*(s*2^a)) :=
  groupTable (doubleIndex (groupIndex e _)) test (fun k => rowTable (checkEquiv a s) (checkEquiv a s) (T k))

@[simp] theorem calls_labelTable {s a : ℕ} (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (T : Signature m → CheckRows a s) : (labelTable e test T).calls = 4*N*(s*2^a)*A := by
  rw [labelTable, calls_groupTable]
  ring

theorem groupRows_labelTable {s a : ℕ} (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (T : Signature m → CheckRows a s) (v : L) (x z : Bank A h (N*(s*2^a))) :
    groupRows (doubleIndex (groupIndex e _)) v ((labelTable e test T).applyAt h (Fin.append x z)) =
      (spectralCheckTable (test v) T).applyAt h
        (Fin.append (groupRows (groupIndex e _) v x) (groupRows (groupIndex e _) v z)) := by
  rw [labelTable, groupRows_groupTable, groupRows_append]
  rfl

/-- Finite shared pencil and repair template in ordinary instructions. -/
def compiledLabelBatch (hm : 2 ≤ m) (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (p : Plan A (N*basisWidth m) (N*basisWidth m)) : Plan A (N*basisWidth m) (N*basisWidth m) :=
  hermite (p.iterate (clockPeriod m)) (labelMix e (generatedChecks m))
    (labelMix e (generatedChecks m)ᵀ) (labelTable e test (batchTable m hm))

theorem calls_compiledLabelBatch (hm : 2 ≤ m) (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (p : Plan A (N*basisWidth m) (N*basisWidth m)) :
    (compiledLabelBatch hm e test p).calls = 4*clockPeriod m*p.calls+4*N*basisChecks m*A := by
  simp only [compiledLabelBatch, calls_hermite, calls_iterate, calls_labelMix, calls_labelTable,
    basisChecks]
  ring

/-- All data rows receive their label's exact product multiplier in frequency
space after the shared predictor, the independent correction tables and the
last shared predictor. -/
theorem frequency_compiledLabelBatch (hm : 2 ≤ m) (e : L ≃ Fin N) (test : L → Column A → Signature m)
    (p : Plan A (N*basisWidth m) (N*basisWidth m))
    (hp : ∀ v (x : Bank A h (N*basisWidth m)) (y : Addr A h),
      labelSlice e v y (p.applyAt h x) = stageMatrix hm (∑ j, test v (y j)) *ᵥ labelSlice e v y x)
    (v : L) (x : Bank A h (N*basisWidth m)) (y : Addr A h) :
    labelSlice e v y ((compiledLabelBatch hm e test p).applyAt h x) =
      (∏ t, (-1 : ℚ)^((∑ j, test v (y j)) t).val) • labelSlice e v y x := by
  let k := ∑ j, test v (y j)
  let idx := rowIndex m (clockDigits m) (clockPeriod m)
  let B := flattenRat (diagonal (generatedPrediction hm k))
  let H := generatedChecks m
  let t := batchTable m hm k
  let ei (j : Fin (batchWidth m) × Coord (batchExponent m)) :=
    groupIndex e _ (v,finProdFinEquiv j)
  let ej (j : Fin (batchChecks m) × Coord (batchExponent m)) :=
    groupIndex e _ (v,finProdFinEquiv j)
  have hb : ∀ z, slice ei y ((p.iterate (clockPeriod m)).applyAt h z) = B *ᵥ slice ei y z := by
    intro z
    rw [slice_iterate ei y p (stageMatrix hm k) (fun w => hp v w y)]
    exact congrArg (· *ᵥ slice ei y z) (rationalStage_pow idx _ (batchPencil_good m hm) k)
  let T := labelTable e test (batchTable m hm)
  have h₁ (u z : Bank A h (N*basisChecks m)) :
      slice ej y (leftPart (T.applyAt h (Fin.append u z))) =
      flattenRat t.toBlocks₁₁ *ᵥ slice ej y u + flattenRat t.toBlocks₁₂ *ᵥ slice ej y z := by
    change frequencyRows (groupRows (groupIndex e _) v (leftPart _)) y = _
    rw [groupRows_leftPart, groupRows_labelTable]
    exact funext fun j => frequency_spectralCheck_left (test v) (batchTable m hm) _ _ j y
  have h₂ (u z : Bank A h (N*basisChecks m)) :
      slice ej y (rightPart (T.applyAt h (Fin.append u z))) =
      flattenRat t.toBlocks₂₁ *ᵥ slice ej y u + flattenRat t.toBlocks₂₂ *ᵥ slice ej y z := by
    change frequencyRows (groupRows (groupIndex e _) v (rightPart _)) y = _
    rw [groupRows_rightPart, groupRows_labelTable]
    exact funext fun j => frequency_spectralCheck_right (test v) (batchTable m hm) _ _ j y
  apply Eq.trans (slice_hermite ei ej y _ _ _ T B
    (flattenRat H) (flattenRat Hᵀ) (flattenRat t.toBlocks₁₁) (flattenRat t.toBlocks₁₂)
    (flattenRat t.toBlocks₂₁) (flattenRat t.toBlocks₂₂) hb
    (fun z => frequency_labelMix e H v z y) (fun z => frequency_labelMix e Hᵀ v z y) h₁ h₂ x)
  have he := action _ _ _ _ (generated_certificate hm k) (slice ei y x)
  dsimp only at he
  rw [baseTarget_rat] at he
  exact he

end KernelPass.Plan

end NearSquareRoot
end Computability
end OAI
