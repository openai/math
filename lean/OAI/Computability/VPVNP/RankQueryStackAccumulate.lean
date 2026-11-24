import OAI.Computability.VPVNP.RankQueryStackNativeFrames
import OAI.Computability.VPVNP.SliceArithmeticMultiplyAccumulate
import OAI.Computability.VPVNP.StructuredStackCount

/-! # Extension-field multiply-and-add on native Schur scalars -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Scalar

open SliceArithmetic
open SliceArithmeticRound (packed)
open MultiplyAccumulate

variable {p e v : ℕ} [Fact p.Prime] [NeZero e]

/-- The public stacks of the Schur multiply-and-add callback. -/
def accumulateFrame (c : Vector p e) (v : ℕ) (left returned acc : Scalar c) : RAMTape.Stacks Port :=
  clean (external p e v (packed v (List.ofFn c)) (Engine.scalar v left) (Engine.scalar v returned)
    (Engine.scalar v acc))

theorem accumulate_runs (hw : Word.workingWidth p ≤ v) (c : Vector p e) (left returned acc : Scalar c) :
    ∃ t ≤ callCap e v, machine.Runs t (accumulateFrame c v left returned acc)
      (accumulateFrame c v left returned (acc + left * returned)) := by
  have hd : (acc + left * returned).digits = add acc.digits (mul c left.digits returned.digits) := by
    rw [product_eq]
    change (pack c (add acc.digits (pack c (mul c left.digits returned.digits)).digits)).digits = _
    simp
  simpa only [accumulateFrame, Engine.scalar, hd] using machine_runs (NeZero.pos e) hw c
    left.digits returned.digits acc.digits

/-- The deterministic arithmetic call transfers control once, deducting its
actual running time from the remaining budget. -/
theorem accumulate_count (hw : Word.workingWidth p ≤ v) (c : Vector p e) (left returned acc : Scalar c) :
    ∃ t ≤ callCap e v, ∀ (continuation : ℕ → RAMTape.Stacks Port → ℕ) (fuel : ℕ),
      machine.body.count continuation (fuel + t) (accumulateFrame c v left returned acc) =
        continuation fuel (accumulateFrame c v left returned (acc + left * returned)) := by
  obtain ⟨t, ht, run⟩ := accumulate_runs hw c left returned acc
  exact ⟨t, ht, run.count_eq⟩

end RankQuery.Stack.Scalar

end VPVNP
end Computability
end OAI
