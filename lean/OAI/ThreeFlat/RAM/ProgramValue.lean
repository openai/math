import OAI.ThreeFlat.RAM.ProgramBits
import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Weighted execution of the program stored in its own input -/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {F : Type*} [Semiring F] {w p r k q : ℕ}

/-- Read the program from the prefix and execute it with all the same bits
accessible to ordinary external-memory instructions. A malformed entry rejects. -/
def adviceValue (code : FieldCode F w) (p r k : ℕ)
    (fits : (1 + 6*p + k)*w ≤ q) (D : Fin q → Bool)
    (fuel : ℕ) (state : Word w) (base : ℕ) (input : Memory w) : F :=
  match readAdvicePrefix w p r k fits D with
  | none => 0
  | some P => value code P fuel state (memoryWithAdvice base D input)

theorem adviceValue_install (code : FieldCode F w) (M : Machine w p r k)
    (h : TextFits w p r k) (fits : (1 + 6*p + k)*w ≤ q) (tail : Fin q → Bool)
    (fuel : ℕ) (state : Word w) (base : ℕ) (input : Memory w) :
    adviceValue code p r k fits (installProgram M tail) fuel state base input =
      value code M fuel state (memoryWithAdvice base (installProgram M tail) input) := by
  simp [adviceValue, readAdvicePrefix_install M h]

end ThreeFlat.RAM

end OAI
