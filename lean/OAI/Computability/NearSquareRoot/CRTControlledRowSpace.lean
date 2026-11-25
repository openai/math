import OAI.Computability.NearSquareRoot.CRTControlledBudget
import OAI.Computability.NearSquareRoot.CRTControlledSpace

/-! # Time and linear workspace for independent packed rows

Apply a single packed P192 program on all rows after the low payload and high row
selector have been chosen. The low fields pay for polynomial metadata work, and the
high fields allow the entire peak of the active row to fit in stream volume.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip NearSquareRoot.Space
open IntegerMultiplication.Code.Task (forest)

/-- A joint physical time/space bound from an ordinary P192 packed-row program.
The same program is used on every row before it is lifted to the bounded outer scan. -/
theorem packedRowsTimeSpace {X : Type} {r : Regime X} {records packed : X → ℕ}
    {rate : X → ℝ} {p q : X → Tree} (row : Breeze rate r records packed p q) :
    ∃ degree : ℕ, ∀ {Y : Type} (rows width factor volume k R : Y → ℕ)
      (pick : ((y : Y) × Fin (rows y)) → X) (input output : Y → ℕ → Tree),
      (∀ z, r.scale (pick z) ≤ k z.1) →
      (∀ y, 0 < R y) →
      (∀ z, 2^(payloadBits degree (k z.1)) * R z.1 ≤ packed (pick z)) →
      (∀ z, records (pick z) * packed (pick z) ≤ width z.1) →
      (∀ z, 2 * rate (pick z) ≤ factor z.1) →
      (∀ z : (y : Y) × Fin (rows y), input z.1 z.2.val = p (pick z)) →
      (∀ z : (y : Y) × Fin (rows y), output z.1 z.2.val = q (pick z)) →
      (∀ y, (forest (input y) (List.range (rows y))).count ≤ volume y) →
      (∀ y, (forest (output y) (List.range (rows y))).count ≤ volume y) →
      (∀ y, rows y * width y ≤ volume y) → (∀ y, factor y ≤ rows y) →
      BoundedTask (fun y => volume y * factor y + 5*volume y + 2)
        (fun y => 4*volume y + 3)
        (fun y => forest (input y) (List.range (rows y)))
        (fun y => forest (output y) (List.range (rows y))) := by
  obtain ⟨degree, runs⟩ := physicalPayloadBound row
  refine ⟨degree, ?_⟩
  intro Y rows width factor volume k R pick input output scale hR hw hvol hr hp hq hIn hOut hsize hrows
  have exec := runs pick (fun z => k z.1) (fun z => R z.1) scale (fun z => hR z.1) hw
  have typed : Carries (fun z : (y : Y) × Fin (rows y) => ((width z.1 * factor z.1 : ℕ) : ℝ))
      (p ∘ pick) (q ∘ pick) := by
    apply exec.larger
    intro z
    have hv : (records (pick z) : ℝ) * (packed (pick z) : ℝ) ≤ width z.1 := by exact_mod_cast hvol z
    have hh := mul_le_mul hv (hr z) (show 0 ≤ 2*rate (pick z) by linarith [row.1 (pick z)])
      (Nat.cast_nonneg (α := ℝ) (width z.1))
    push_cast
    linarith
  have same : Carries (fun z : (y : Y) × Fin (rows y) => ((width z.1 * factor z.1 : ℕ) : ℝ))
      (fun z => input z.1 z.2.val) (fun z => output z.1 z.2.val) := by
    simpa only [funext hp, funext hq, Function.comp_def] using typed
  exact physicalRowsOfCarries rows width factor volume input output same hIn hOut hsize hrows

end Controlled

end NearSquareRoot
end Computability
end OAI
