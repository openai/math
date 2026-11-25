import OAI.Computability.NearSquareRoot.KernelPassRectSpectrum
import OAI.Computability.NearSquareRoot.KernelPassLabelRepair

/-! # Labelwise frequency action of the routed binary predictor

The rectangle program numbers its entire row bank at once. The repair
program numbers a label, an extension row, and its basis component in order.
Their exact frequency semantics agree through the fixed row permutation. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Matrix Finset PencilSearch PencilDescent CyclotomicCode

variable {A h m N : ℕ} {L : Type} [Fintype L] [DecidableEq L]

abbrev StageRow (m : ℕ) := Fin (batchWidth m) × Coord (batchExponent m)

/-- Number the labels, then the extension rows, then their basis components. -/
def stageIndex (e : L ≃ Fin N) (m : ℕ) : L × StageRow m ≃ Fin (N*Plan.basisWidth m) :=
  (e.prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- A simultaneous labelled pencil, specified by its rational blocks, acts
on every labelled bank in the coordinate convention of the Hermite program. -/
theorem labelSlice_stage (hm : 2 ≤ m) (e : L ≃ Fin N)
    (p : On A (L × StageRow m) (L × StageRow m))
    (B₀ : StageRow m → StageRow m → ℚ) (B : Fin m → StageRow m → StageRow m → ℚ)
    (sig : L → Addr A h → Signature m) (H : Fin m → L → Mat A h)
    (hblock : ∀ (w v : L) (k l : StageRow m),
      block (I := L × StageRow m) (O := L × StageRow m) p h (w,k) (v,l) =
        if w = v then B₀ k l • (1 : Mat A h) + ∑ j, B j k l • H j w else 0)
    (hspectral : ∀ j w (v : Addr A h → ℚ) y,
      (Plan.walshMatrix A h *ᵥ (H j w *ᵥ v)) y =
        (-1 : ℚ)^((sig w y) j).val * (Plan.walshMatrix A h *ᵥ v) y)
    (hcoeff : ∀ (t : Signature m) (k l : StageRow m),
      B₀ k l + ∑ j, ((-1 : ℚ)^(t j).val) * B j k l = Plan.stageMatrix hm t k l)
    (w : L) (x : Bank A h (N*Plan.basisWidth m)) (y : Addr A h) :
    Plan.labelSlice e w y ((renumber (stageIndex e m) p).applyAt h x) =
      Plan.stageMatrix hm (sig w y) *ᵥ Plan.labelSlice e w y x := by
  funext k
  change Plan.frequency ((renumber (stageIndex e m) p).applyAt h x) (stageIndex e m (w,k)) y =
    ∑ l, Plan.stageMatrix hm (sig w y) k l * Plan.frequency x (stageIndex e m (w,l)) y
  rw [atFrequency (stageIndex e m) p B₀ B H (fun j v z => (-1 : ℚ)^((sig v z) j).val)
    hblock hspectral]
  simp only [hcoeff]
  exact sum_congr (Finset.ext (fun _ => ⟨fun _ => mem_univ _, fun _ => mem_univ _⟩)) (fun _ _ => rfl)

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
