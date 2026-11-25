import OAI.Computability.NearSquareRoot.FixedCandidateCRTRouting

/-! # Packed table stages rendered in the original Dusk record order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code DigitPacking FixedPoint

noncomputable section

variable {n : ℕ} (h : Directory n)

abbrev Packed (n : ℕ) (s : Switch n) :=
  CRTTable.Packed (BoxFin.modulus (box n)) (CRTTable.axisWidth (box n)) s.1.val

def packing (s : Switch n) : Fin (capacity n) ≃ Packed n s :=
  letI := BoxFin.modulus_neZero h
  (index h).symm.trans (CRTTable.packAddress _ _ (fits h) s.1.val)

def packedSlot (inv : Bool) (s : Switch n) : Equiv.Perm (Packed n s) :=
  letI := BoxFin.modulus_neZero h
  Benes.packedStage _ (CRTTable.packedTables _ _ (fits h) s.1.val inv) s.2

/-- Render a depth-dependent array in physical record order, retaining the length ruler. -/
def render (s : Switch n) (v : Packed n s → Record (addressBits n)) :=
  framed (v ∘ packing h s)

def pack (s : Switch n) (r : Array n) : Packed n s → Record (addressBits n) :=
  r ∘ (packing h s).symm

@[simp] theorem render_pack (s : Switch n) (r : Array n) : render h s (pack h s r) = framed r := by
  unfold render pack
  congr 1
  funext i
  simp

/-- After an arbitrary physically packed Beneš half-stage, re-reading the Dusk tape
gives exactly the single natural record-index permutation used by the enclosing sweep. -/
theorem render_scatter (inv : Bool) (s : Switch n) (r : Array n) :
    render h s (Benes.scatter (packedSlot h inv s) (pack h s r)) =
      framed (step h inv r s) := by
  unfold render pack framed step
  rfl

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
