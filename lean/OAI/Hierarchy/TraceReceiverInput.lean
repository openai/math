import OAI.ThreeFlat.Diagonal.NativeTrace
import OAI.ThreeFlat.RAM.TickHeaderShift

namespace OAI
/-! # Initializing the receiving pin frame from the actual self-programmed tape -/

namespace Hierarchy.TraceFactorReceiver

open ThreeFlat Diagonal RAM
open Computability.VPVNP Computability.VPVNP.BurstRAM PrivateRAM RAMMemory

variable {w pc regs slots p : ℕ}

def inputMemory (M : Machine w pc regs slots) (p : ℕ) (input : ℕ → Bool) : Memory w :=
  memoryWithAdvice 0 (NativeTrace.executable M)
    (initialMemory p (fun j => TraceBitHeader.binaryWord w (input j)))

theorem raw_input (M : Machine w pc regs slots) (input : ℕ → Bool)
    (fits : (1+6*pc+slots)*w ≤ p)
    (authentic : ∀ i : Fin ((1+6*pc+slots)*w), input i.val = NativeTrace.executable M i) :
    inputMemory M p input = TickHeaderShift.initial w (fun i : Fin p => input i.val) := by
  unfold inputMemory
  rw [TickMountedPins.advice_agrees]
  · funext a
    by_cases h : a < p <;> cases bit : input a <;>
      simp [TickHeaderShift.initial,initialMemory,h,bit,TraceBitHeader.binaryWord,BitLayout.bitWord]
    all_goals exact Fin.ext rfl
  · intro i
    have hi := i.isLt.trans_le fits
    simp only [Nat.zero_add,initialMemory,ite_eq_left hi,TraceBitHeader.binaryWord,authentic i]

/-- Thirty-seven instructions of fixed text execute the full initial pin
relocation. The pad and hidden part of the new frame are zero afterwards. -/
theorem mount_input (M : Machine w pc regs slots) (input : ℕ → Bool)
    (fits : (1+6*pc+slots)*w ≤ p)
    (authentic : ∀ i : Fin ((1+6*pc+slots)*w), input i.val = NativeTrace.executable M i) (room : 2+p+p < 2^w) :
    (TickHeaderShift.procedure w p).Spec (fun m => m=inputMemory M p input)
      (fun _ out => out=TickMountedPins.memory (w:=w) (fun i : Fin p => input i.val)) (28+16*p) := by
  rw [raw_input M input fits authentic]
  exact TickHeaderShift.spec _ room

end Hierarchy.TraceFactorReceiver

end OAI
