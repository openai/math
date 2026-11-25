import OAI.Computability.NearSquareRoot.PhysicalWalshXorNativeCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorOpcodeTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshXorGateTotal

/-! # Total execution of the canonical native XOR gate

The opcode is wrapped with the same fixed headers and row commands as in
the quantitative gate. Its finite runtime suffices at every actual window
width, independently of the reserve estimates used elsewhere in the plan.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram NamedPacked CommonRegisters GeneratorSyntax Filter

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x))

/-- The chosen row disassembly and collection commands work with any total
native row implementation on the actual payload. -/
theorem windowCmd_total (op : X → Op) (f : (x:X) → Input (P x) (k x) (U x)) {native : Cmd}
    (row : NativeRowTotal r P k hP u native op f) :
    ∃ t s, EffectiveBoundedTask.Runs (windowCmd r P k hP hk u op f native) t s
      (fun x => .fork (r.header x) (store (u x) (f x)))
      (fun x => store (u x) (rewired P k op f x)) := by
  let ends := rowEnds r P k hP hk u f (rewired P k op f)
  exact opcodeTotal r P k hP u op f (e:=ends.choose_spec.choose_spec.choose)
    ends.choose_spec.choose_spec.choose_spec row

/-- The opcode stage for a canonical program which terminates on every valid call. -/
theorem stagesTotalFromCanonical {native : Cmd}
    (h : ∃ time : Call id → ℕ, EffectiveTask.Runs native time Call.input Call.output) :
    StagesTotal r P k u (stageCmd r P k hP hk u native) := by
  obtain ⟨time,run⟩ := h
  let world := opRegime r P k hk U
  let code (j : OpWorld P k U) := j.2.1.val
  let data (j : OpWorld P k U) := j.2.2
  have prep := (nativeRowsFromCanonical world _ _ (opPrefix r P k hk U hP)
    (opWidth r P k hk U) code (opInstruction r P k hk U) (opValid P k U)
    (fun j => u j.1) data).choose_spec.2 native time run
  exact windowCmd_total world _ _ (opPrefix r P k hk U hP) (opWidth r P k hk U)
    (fun j => u j.1) code data prep

/-- The full forest with this specific canonical opcode runs on every physical window. -/
theorem gateTotalFromCanonical {native : Cmd}
    (h : ∃ time : Call id → ℕ, EffectiveTask.Runs native time Call.input Call.output) :
    GateTotal r P k u (gateCmd r k hk (stageCmd r P k hP hk u native)) :=
  StagesTotal.gateTotal hk (stagesTotalFromCanonical r P k hP hk u h)

/-- Any finite quantitative canonical opcode certificate gives unconditional gate
correctness, even if its claimed outer reserve is smaller than its true row cost. -/
theorem gateTotalFromOpAt {native : Cmd} {ρ : ℝ} (h : OpAt native ρ id) :
    GateTotal r P k u (gateCmd r k hk (stageCmd r P k hP hk u native)) := by
  obtain ⟨_,_,carry⟩ := h
  obtain ⟨t,run,_⟩ := carry.work
  exact gateTotalFromCanonical r P k hP hk u ⟨t,run⟩

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
