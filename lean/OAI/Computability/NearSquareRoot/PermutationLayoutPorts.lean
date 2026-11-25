import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryOffsets
import OAI.Computability.NearSquareRoot.CRTControlledFlatNumber

/-! # Field-port coordinates in the physical binary address -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin
open IntegerMultiplication IntegerMultiplication.Adic

variable {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box) (hd : 4 ≤ box.length)

/-- The local Beneš field ports cover the complete tape address, with MSB order
inside a field and increasing bit offsets between fields. -/
def packedPort : (Σ j : Fin (box.length/4), Fin (physicalWidth (box := box) j)) ≃ Fin k :=
  Benes.FieldDirectory.finitePort _ (sum_physicalWidth hb hd)

theorem packedPort_val (j : Fin (box.length/4)) (r : Fin (physicalWidth (box := box) j)) :
    (packedPort hb hd ⟨j,r⟩).val =
      blockOffset (box := box) j + (physicalWidth (box := box) j-1-r.val) :=
  Benes.FieldDirectory.finitePort_val _ _ j r

variable [∀ i, NeZero (modulus box i)]

theorem packedRecord_blockBit (y : Block 2 k) (j : Fin (box.length/4))
    (r : Fin (physicalWidth (box := box) j)) :
    ((packedRecord hb hd (Controlled.flatAddress 2 k y)).2 j) r =
      Controlled.prefixBit y (packedPort hb hd ⟨j,r⟩) := by
  rw [packedRecord_port, ← packedPort_val hb hd]
  simpa using (Controlled.prefixBit_address (Controlled.flatAddress 2 k y) (packedPort hb hd ⟨j,r⟩)).symm

end BoxFin

end NearSquareRoot
end Computability
end OAI
