import OAI.Computability.NearSquareRoot.SynchronizedAxisWord

/-! # Expanding local pair stages into unconditional Walsh and phase slots

The same unary record format is used for the expanded program. The first added
Walsh (10) acts on the half selector. The other (14) uses the exposed internal
radix bit on both halves. Each has three corresponding phase opcodes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord

/-- Expand one forward-oriented interleaved Walsh/diagonal template. -/
def threeRounds (walshTag firstPhase : ℕ) (arg : IntegerMultiplication.Code.Tally) : List Inst :=
  [inst walshTag arg, inst firstPhase arg, inst walshTag arg, inst (firstPhase+1) arg,
    inst walshTag arg, inst (firstPhase+2) arg]

/-- Adjoint templates reverse the six instructions and conjugate the three phase tables. -/
def lowerInst (x : Inst) : List Inst :=
  let orient := fun w => if x.2.2 then adj w else w
  if x.1.length = 2 then orient (threeRounds 14 15 x.2.1)
  else if x.1.length = 3 then orient (threeRounds 10 11 x.2.1)
  else [x]

def lower (w : List Inst) : List Inst := w.flatMap lowerInst
def loweredRestored (k : IntegerMultiplication.Code.Tally) : List Inst := lower (restored k)

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
