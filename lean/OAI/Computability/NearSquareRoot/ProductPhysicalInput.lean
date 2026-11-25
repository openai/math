import OAI.Computability.NearSquareRoot.ProductRecovery
import OAI.Computability.NearSquareRoot.PrecisionDigitEncoding

/-! # The input packet of the rounded multiplication program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open IntegerMultiplication DigitPacking

variable (x : Bits.Word) (h : ValidShape x.length) [∀ i, NeZero (BoxFin.modulus (inputBox x) i)]
  [NeZero (∏ i, BoxFin.modulus (inputBox x) i)]

/-- The concrete parser and balanced CRT permutation produce the record at
every physical input address of the rounded multiplication program. -/
theorem encoded_inputRecords (hn : 2 ≤ x.length) :
    List.ofFn (fun j : Fin (capacity x.length) =>
      ((encodedBoxed x)[((BoxFin.crtSlotPerm h).symm j).val]?).getD ([],[])) =
      List.ofFn (fun j : Fin (capacity x.length) =>
        Dusk.mark (inputRecords _ (BoxFin.padding (inputBox x)) (BoxFin.pairwise h) x.length x
          ((BoxFin.recordIndex h).symm j))) :=
  encoded_after_crt x h hn

end ProductRecovery

end NearSquareRoot
end Computability
end OAI
