import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowData
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # Unrestricted termination of the native Walsh XOR row command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication Code

/-- Erasing the workspace estimate preserves the specified command and its clock. -/
theorem EffectiveBoundedTask.Runs.withoutSpace {I : Type} {c : Cmd} {t s : I → ℕ} {u v : I → Tree}
    (h : EffectiveBoundedTask.Runs c t s u v) : EffectiveTask.Runs c t u v :=
  command_contract c from h.task.forget

namespace PhysicalWalsh.XorWindow

open Adic Strip Staff Loom Packed Controlled Controlled.PositionProgram NamedPacked

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P)
    {U : X → Type} (u : (x:X) → Series (U x))

/-- On every high prefix the physical native command reorders the actual
payload cells, allowing its clock to depend on this very row. -/
def NativeRowTotal (c : Cmd) (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x)) : Prop :=
  let rr := fixedRowRegime r P hP
  let bits (z : (x:X) × Block 2 (P x)) := k z.1
  let s z := line 2 (bits z)
  let payload (z : (x:X) × Block 2 (P x)) := u z.1
  let read (z : (x:X) × Block 2 (P x)) (b : Block 2 (bits z)) := f z.1 (prefixBit b) z.2
  ∃ t, EffectiveTask.Runs c t (together rr.header (cloth s payload read)) (cloth s payload (fun z b =>
    read z (nativeOp (bits z) (guardWidth (bits z)) (op z.1) b)))

theorem NativeRowAt.total {c : Cmd} {ρ : ℝ} {op : X → Op} {f : (x:X) → Input (P x) (k x) (U x)}
    (h : NativeRowAt r P k hP u c ρ op f) : NativeRowTotal r P k hP u c op f := by
  obtain ⟨_,_,carry⟩ := h
  obtain ⟨t,run,_⟩ := carry.work
  exact ⟨t,run⟩

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
