import OAI.Computability.NearSquareRoot.InterchangeBeadBreeze
import OAI.Computability.NearSquareRoot.InterchangeBeadThreshold
import OAI.Computability.NearSquareRoot.InterchangeRadix
import OAI.Computability.NearSquareRoot.InterchangeBinaryBridge

/-!
# Uniform prime-radix interchange on ordinary P192 bead records
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress.Request NearSquareRoot.InterchangeBinary

/-- The radix is fixed once for the exponent and the prescribed lower bound.
The same recursive program accepts every header and every logical record width. -/
theorem exists_radix_beads {α : ℝ} (hα : 1/2 < α) (threshold : ℕ) :
    ∃ b : ℕ, b.Prime ∧ threshold < b ∧ ∀ {I : Type} (r : Regime I), RadixBeads b r α := by
  obtain ⟨p,b,prime,_,base,large,solver⟩ := exists_radix_interchange hα threshold
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨k,run⟩ := solver (beadDigit (F:=ZMod p)) beadDigit_injective
  refine ⟨b,base,large,?_⟩
  intro I r P G B e pos he hp hg hb hbound L T u fit v
  obtain ⟨pad,header,dom,thick⟩ := bead_threshold P G B e hp hg hb he hbound k
  exact radixBeadBreeze base.two_le (by linarith) k run P G B e pos he hp hg hb hbound
    L u fit v pad header dom thick

end InterchangePayload

end NearSquareRoot
end Computability
end OAI
