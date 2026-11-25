import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.Diagonal.SlotImage
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.TraceSourceFibers

namespace OAI
/-! # Native site, lane and clipped paired-pin ordinals of the initial cursor -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block
open Computability.VPVNP.Compression LaneCursor
open scoped Classical
variable {F : Type} [Field F] (B : Block F) {k : ℕ} (hk : 2≤k) (low offsets slots : ℕ)

def cursorOrdinal (i : Fin k) (L : Lane k) :=
  SlotImage.siteOrdinal (B.cursorState hk low offsets slots).order
    (CompressorPacking.Native.tagOrdinal k) (i,L)

theorem cursorOrdinal_eq (i : Fin k) (L : Lane k) :
    B.cursorOrdinal hk low offsets slots i L=i.val*2^k+(finFunctionFinEquiv L).val := rfl

theorem cursorOrdinal_div (i : Fin k) (L : Lane k) :
    B.cursorOrdinal hk low offsets slots i L/2^k=i.val := by
  rw [cursorOrdinal_eq]; exact TraceSourceOwner.pack_div (finFunctionFinEquiv L).isLt

theorem cursorOrdinal_mod (i : Fin k) (L : Lane k) :
    B.cursorOrdinal hk low offsets slots i L%2^k=(finFunctionFinEquiv L).val := by
  rw [cursorOrdinal_eq]; exact TraceSourceOwner.pack_mod (finFunctionFinEquiv L).isLt

theorem cursorOrdinal_ext (S : ℕ) (i : Fin k) (L : Lane k) :
    (if B.cursorOrdinal hk low offsets slots i L/2^k=0 then
        min (2*2^low) (S-(B.cursorOrdinal hk low offsets slots i L%2^k)*(2*2^low)) else 0) =
      (if i.val=0 then TraceSourceOwner.pinCount S 1 low (finFunctionFinEquiv L).val else 0) := by
  simp [cursorOrdinal_div,cursorOrdinal_mod,TraceSourceOwner.pinCount,TraceSourceOwner.pinSpan]

end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
