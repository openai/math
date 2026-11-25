import OAI.Computability.NearSquareRoot.SynchronizedBoxBatchProgram
import OAI.Computability.NearSquareRoot.SynchronizedBatchSlots
import OAI.Computability.NearSquareRoot.SynchronizedScheduleSemantics

/-! # The synchronized opcode tape of the computed coprime box

The fixed machine receives one direction bit and a unary width. It computes
the coprime axes, borrows the prescribed fibers in fifteen batches per axis,
lowers each conditional Walsh to its eight microinstructions, and interleaves
the resulting words. In the adjoint direction the descriptors are read in
reverse order and each one carries the adjoint bit.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Staff IntegerMultiplication.Strip
open SynchronizedLayers.ScheduleProgram SynchronizedBlocks

/-- The computed maximum local depth after physical lowering. -/
def boxDepth (k : ℕ) : ℕ := 8 * (7 * (15 * (18 * (1032 * (BoxScale.width k + 1) + 1549))))

def boxPlan (u : Tally) : List (Row SlotDescriptor) :=
  plan slotKind ((boxWords u).map localSlots, tally (boxDepth u.length))

/-- Tag all rows with direction and reverse them for the adjoint transform. -/
def orientRows {X : Type} (p : Bool × List X) : List (Bool × X) :=
  polyPush id (p.1, bif p.1 then p.2.reverse else p.2)

def directedPlan (p : Bool × Tally) : List (Bool × Row SlotDescriptor) :=
  orientRows (p.1,boxPlan p.2)

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
