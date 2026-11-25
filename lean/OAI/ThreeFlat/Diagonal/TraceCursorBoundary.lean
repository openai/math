import OAI.ThreeFlat.Diagonal.TraceCursorFactor
import OAI.ThreeFlat.Diagonal.HistoryWordLayout
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts

namespace OAI
/-! # The two physical native port words at each cursor -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage.Block

open Computability.VPVNP.Compression CompressorPacking LaneCursor LaneCursor.RowLayout HistoryContraction LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
variable {F : Type} [Field F] (B : Block F) {q : ℕ} (hk : 2 ≤ q+1) (low offsets slots : ℕ)

local notation "A" => B.cursorState hk low offsets slots
local notation "D" => PayloadAddress low slots
local notation "O" => Fin offsets
local notation "W" => 2^low*(offsets*slots*3)

/-- These are the two slots in the native physical half-record order. -/
theorem cursorOutPort_native (i : Fin (q+1)) (L : Lane (q+1)) (s : Fin ((B.cursorCopies+1)*2)) :
    B.cursorOutPort hk low offsets slots i L s =
      Native.ShrinkStage.Halves.outbound (A).graph (A).chart (i,L) (Fin.cast B.cursor_degree s) := rfl

theorem cursorInPort_native (i : Fin (q+1)) (L : Lane (q+1)) (s : Fin ((B.cursorCopies+1)*2)) :
    B.cursorInPort hk low offsets slots i L s =
      Native.ShrinkStage.Halves.inbound (A).graph (A).chart (i,L) (Fin.cast B.cursor_degree s) := rfl

theorem cursorOut_read (i : Fin (q+1)) (L : Lane (q+1)) (x : (A).shape.Half (i,L))
    (s : Fin ((B.cursorCopies+1)*2)) (tag : O×D) :
    B.cursorOut hk low offsets slots i L x s tag =
      (MotifBinaryPacking.word W).symm
        (x (Native.ShrinkStage.Halves.outbound (A).graph (A).chart (i,L) (Fin.cast B.cursor_degree s)))
        (((tagOrder offsets low slots).symm tag).cast (by ac_rfl)) := rfl

theorem cursorIn_read (i : Fin (q+1)) (L : Lane (q+1)) (x : (A).shape.Half (i,L))
    (s : Fin ((B.cursorCopies+1)*2)) (tag : O×D) :
    B.cursorIn hk low offsets slots i L x s tag =
      (MotifBinaryPacking.word W).symm
        (x (Native.ShrinkStage.Halves.inbound (A).graph (A).chart (i,L) (Fin.cast B.cursor_degree s)))
        (((tagOrder offsets low slots).symm tag).cast (by ac_rfl)) := rfl


end ThreeFlat.Diagonal.PhysicalStage.Block

end
end OAI
