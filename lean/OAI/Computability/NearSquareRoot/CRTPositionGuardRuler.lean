import OAI.Computability.NearSquareRoot.CRTControlledSizes
import OAI.Computability.IntegerMultiplication.Carry.Figure

/-! # Charged unary parameters for the guarded position permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication.Carry IntegerMultiplication.Staff IntegerMultiplication.Strip

variable {I : Type} {r : Regime I} {k : I → ℕ}

theorem guardWidth_realizes (hk : Realizes r k) :
    Realizes r (fun x => guardWidth (k x)) :=
  (Realizes.fix 7).plus ((Realizes.fix 2).times
    (Figure.of_spoken (hk.plus (Realizes.fix 1))).short_log)

theorem third_realizes (hk : Realizes r k) :
    Realizes r (fun x => k x / 3) :=
  hk.dividing (Realizes.fix 3)

theorem thirdRemainder_realizes (hk : Realizes r k) :
    Realizes r (fun x => k x % 3) :=
  hk.rem (Realizes.fix 3)

end Controlled

end NearSquareRoot
end Computability
end OAI
