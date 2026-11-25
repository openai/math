import OAI.Hierarchy.DescentSeedScalarSelectors
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # Decoding census counts from the original ballot bits -/
namespace Hierarchy.DescentSeedRoot
open Catalyst ThreeFlat.Diagonal Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s : ℕ}

/-- A word is determined by its little-endian digits. -/
def bitWord (d : ℕ) : Word d ≃ (Fin d→Bool) :=
  Equiv.ofBijective TraceWords.bits ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨TraceWords.bits_injective, by simp [Word]⟩)

/-- Decode the full count across all of its low physical bits. -/
def rawCount (z : Select X R s→Bool) (key : CountKey X R) : Word (digitsNeeded s) :=
  (bitWord (digitsNeeded s)).symm (fun b=>z (key,b))

def valid (z : Select X R s→Bool) : Prop := ∀i,(rawCount X z i).val≤ s

theorem raw_digits (z : Select X R s→Bool) (key : CountKey X R) (b : Fin (digitsNeeded s)) :
    (rawCount X z key).val.testBit b.val=z (key,b) :=
  congrFun ((bitWord _).apply_symm_apply (fun b=>z (key,b))) b


end
end Hierarchy.DescentSeedRoot

end OAI
