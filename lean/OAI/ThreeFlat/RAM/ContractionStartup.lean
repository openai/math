import OAI.ThreeFlat.RAM.ContractionGuess

namespace OAI
/-! # Starting the contraction kernel with occupied registers

The six startup instructions initialize the six live input registers. The guess
and cell scans accept every possible initial value in the four scratch registers.
-/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM BitLayout

private def startupRegisters {w : ℕ} (r : Registers w) (param : Fin 5 → Word w) : Registers w :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update r 0 (param 0)) 1 (param 1)) 2 (param 2))
    3 (param 3)) 4 (param 4)) 5 1

private theorem startup_from {F : Type*} [Semiring F] {w : ℕ} (code : FieldCode F w)
    (param : Fin 5 → Word w) (fuel : ℕ) (regs : Registers w) (mem : Memory w) :
    eval code param (fuel + 6) 0 regs mem =
      eval code param fuel 6 (startupRegisters regs param) mem := rfl

/-- From the initial program counter, the contraction kernel returns the network
value with arbitrary starting scratch registers, hidden bits and trailing memory. -/
theorem eval_zero_eq_network {F : Type*} [Fintype F] [Field F] {p w : ℕ}
    (N : BitNetwork F p) (fit : Fits N w) (pin : Fin p → Bool)
    (initialBits : Fin N.internal → Bool) (fuel : ℕ) (regs : Registers w)
    (tailMem : Memory w := fun _ => 0) :
    eval (codec N fit) (parameters N fit) (fuel + 9 + 5*N.internal + 22*N.cells)
        0 regs (memoryWithTail tailMem N (codec N fit) pin initialBits) = N.eval pin := by
  rw [show fuel + 9 + 5*N.internal + 22*N.cells =
      (fuel + 22*N.cells + 3 + 5*N.internal)+6 by omega, startup_from]
  have h := guess_scan N fit pin fuel N.internal (startupRegisters regs (parameters N fit))
    initialBits 0 (Nat.zero_add _) (by simp [startupRegisters, Function.update, parameters])
      rfl rfl rfl rfl rfl tailMem
  simpa only [extensions_zero, BitNetwork.eval] using h

end ThreeFlat.RAM.Contraction

end OAI
