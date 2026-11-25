import OAI.ThreeFlat.Diagonal.TraceBitHeader
import OAI.ThreeFlat.RAM.ProgramBits
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # Public bits used at initialized input addresses -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM RAMMemory
variable {S w : ℕ}

def advicePins {q : ℕ} (base : ℕ) (D : Fin q → Bool) (x : ℕ → Bool) (i : Fin S) : Bool :=
  if h : base ≤ i.val ∧ i.val-base < q then D ⟨_,h.2⟩ else x i.val

theorem adviceWords_inside {q : ℕ} (base : ℕ) (D : Fin q → Bool) (x : ℕ → Bool) (i : Fin S) :
    RAM.memoryWithAdvice base D (initialMemory S (fun a => binaryWord w (x a))) i.val =
      binaryWord w (advicePins base D x i) := by
  by_cases h : base≤i.val ∧ i.val-base<q <;>
    simp [RAM.memoryWithAdvice,h,advicePins,binaryWord,initialMemory,i.isLt]

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
