import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeWordOperands

/-! # Loading the validator's fixed initial word

The word scan used by the private instruction set also loads a fixed natural
literal into an arbitrary bank. Its template gives the word width, and the
two reverse stacks are empty again when the subroutine returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteLiteral

open BurstRAM TapeWord

variable {K : Type}

private def normal {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

/-- Load a fixed natural literal into a word using the operand scanner on the specified ports. -/
def routine (lit : ℕ) (ports : ScanPort → K) : FiniteRoutine K :=
  FiniteRoutine.ofStackCode (Operand.code (Operand.literalBit lit)) ports
    (.clear (Fin.last lit)) normal

theorem runs [DecidableEq K] {w : ℕ} (lit : ℕ) (ports : ScanPort → K)
    (hp : Function.Injective ports) (s : Stacks K) (template : Word w)
    (hs : s (ports .left) = wordBits template) (ht : s (ports .right) = [])
    (hu : s (ports .tmp) = []) :
    (routine lit ports).Runs ((s (ports .out)).length+7*w+3) s
      (Function.update s (ports .out) (wordBits (Fin.ofNat (2^w) lit))) := by
  obtain ⟨q, h⟩ := Operand.literal_run lit template (s (ports .out))
  apply FiniteRoutine.runs_ofStackCode_framed hp (normal := normal) rfl (exit := .done q) rfl
    (fun q hq => by cases q <;> first | rfl | contradiction) h
  · intro p; cases p <;> first | rfl | exact hs | exact ht | exact hu
  · intro p
    cases p <;> simp [Function.update, hp.eq_iff, scanStacks, hs, ht, hu]
  · intro j hj
    exact Function.update_of_ne (Ne.symm (hj .out)) ..

end RAMTape.SiteLiteral

end VPVNP
end Computability
end OAI
