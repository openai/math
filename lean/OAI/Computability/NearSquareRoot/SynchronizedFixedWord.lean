import OAI.Computability.NearSquareRoot.SynchronizedLowerWord

/-! # Routing every butterfly to the same physical bit -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.AxisWord
open IntegerMultiplication.Code

/-- Exchange an internal address bit with the half selector, apply the fixed
Walsh (10), and return both fields. The conditional covers malformed bit indices.
The direction flag is preserved by reversing the whole three-instruction word. -/
def fixedInst (k : Tally) (x : Inst) : List Inst :=
  if x.1.length = 14 then
    if x.2.1.length < k.length then
      let w := [inst 18 x.2.1, inst 10, inst 18 x.2.1]
      if x.2.2 then adj w else w
    else []
  else [x]

def fixedWord (k : Tally) : List Inst := (loweredRestored k).flatMap (fixedInst k)

end ShortFourier.AxisWord

end NearSquareRoot
end Computability
end OAI
