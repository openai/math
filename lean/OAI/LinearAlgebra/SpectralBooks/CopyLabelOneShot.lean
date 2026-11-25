import OAI.LinearAlgebra.SpectralBooks.CopyLabelDegeneration
import OAI.LinearAlgebra.SpectralBooks.CopyLabelOutput
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport
import OAI.LinearAlgebra.SpectralBooks.SpectralSublevels

/-! # Spectral estimate for a single shared-label degeneration -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

noncomputable section
open scoped Classical NNReal

variable {I : Type} [Fintype I] [Nonempty I] {K : Type*} [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop)) (c : ℝ)

omit [Fintype I] [Nonempty I] in
private theorem Raw.grouped_label_ne_zero {D H : Type} [Fintype D] [Fintype H]
    [Nonempty H] [Nonempty D] (σ : H → I) : ((Raw.diagonal H K D).group σ).coeff ≠ 0 := by
  apply ((Raw.diagonal H K D).group_ne_zero_iff σ).mpr
  let d := Classical.arbitrary D
  intro hh
  have hd := congrFun hh (fun _ => d)
  change (Raw.diagonal H K D).coeff (fun _ => d) = (0 : K) at hd
  have he (a : D) : (fun _ : H => d) = (fun _ => a) ↔ d = a :=
    ⟨fun h => congrFun h (Classical.arbitrary H), by rintro rfl; rfl⟩
  simp [Raw.diagonal, he] at hd

/-- Zariski closure of local restrictions is monotone for the log price. -/
theorem rawLogPrice_le_of_restrictionClosure (hc : 0 ≤ c) {X Y : Raw.{0} I K}
    (h : X.coeff ∈ affineZariskiClosure {S | Crossing.IsRestriction S Y.coeff}) :
    rawLogPrice φ c X ≤ rawLogPrice φ c Y := by
  by_cases hX : X.coeff = 0
  · rw [rawLogPrice_zero φ c X hX]
    exact rawLogPrice_nonneg φ hc Y
  apply logPrice_le_of_mem_closure φ h hX hc
  intro U hU _
  exact rawLogPrice_mono φ hc (X := ⟨X.Leg, X.finiteLeg, U⟩) (Y := Y) hU

/-- A diagonal of width `4(q-1)+1` pays for the copy and returns an
independent wire of width `q`. -/
theorem rawLogPrice_copy_one_shot [Infinite K] (hc : 0 ≤ c) (T : Raw.{0} I K)
    (σ : Fin 3 → I) {q : ℕ} (hq : 0 < q)
    (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hmatch : ∀ x, T.coeff x ≠ 0 → hA (x (σ 0)) = hB (x (σ 1))) (hT : T.coeff ≠ 0) :
    rawLogPrice φ c (T.appendLabel (σ 2) (Fin q) (fun x => hA (x (σ 0)))) +
      rawWireDistance φ c (σ 0) (σ 1) * Real.logb 2 q ≤ rawLogPrice φ c T +
      rawLogPrice φ c ((Raw.diagonal (Fin 3) K (Fin 2)).group σ) *
        Real.logb 2 (4 * (q - 1) + 1 : ℕ) := by
  let : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  let L := 4 * (q - 1) + 1
  let w := ![σ 0, σ 1]
  let : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp (Nat.succ_pos _)
  have h := rawLogPrice_le_of_restrictionClosure φ c hc (T.copyOutput_mem_closure σ hA hB hmatch)
  have e := ofRaw_eq_iff.mpr (T.copyOutput_equivalent σ hA)
  have ep := congrArg (fun x : TensorClass I K => c * Real.logb 2 (φ.val x : ℝ)) e
  change rawLogPrice φ c (T.copyOutput σ hA) = rawLogPrice φ c _ at ep
  rw [ep, rawLogPrice_mul φ c _ _ ((T.appendLabel_nonzero_iff ..).mpr hT)
    (Raw.grouped_label_ne_zero w), rawLogPrice_mul φ c T _ hT (Raw.grouped_label_ne_zero σ),
    rawLogPrice_group_diagonal φ w c (α := Fin q),
    rawLogPrice_group_diagonal φ σ c (α := Fin L), Fintype.card_fin, Fintype.card_fin] at h
  exact h

end
end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
