import OAI.Hierarchy.DescentOrdinaryFinalCount
import OAI.Hierarchy.DescentOrdinaryWordTariff
import OAI.Hierarchy.DescentMatcherCountTariff

namespace OAI
/-! # The high pair-count register on the actual ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor w ratio : ℕ)
local notation "a" => v.area

theorem count_word_bill (pos : 0<(a).unit) (wide : 2*(a).unit≤(a).payload)
    (bus : w≤ratio*(a).payload) (short : v.countBits≤(a).payload/2) :
    DateBill.bitTariff (v.counter floor w).program (v.counter floor w).ticks ≤
      2*ratio*(2000*(1+2^((a).k+1)))*DateBill.volumeBits (a).H (a).G (a).payload (a).unit := by
  let p:=(v.area.matcher v.old floor).layout.topology
  have fee:=DateBill.count_words (a).H (a).G (a).payload (a).unit (2^((a).k+1)) w v.countBits p
    (chunkCount (a).shapeAt (a).lanesAt) (v.primitiveEnd floor) short
  have live:=DateBill.words_bits (a).H (a).G (a).payload (a).unit pos wide
  calc
    _ ≤ ((2000*(1+2^((a).k+1)))*DateBill.words (a).H (a).G (a).payload (a).unit)*(ratio*(a).payload) :=
      Nat.mul_le_mul fee bus
    _ = ratio*(2000*(1+2^((a).k+1)))*(DateBill.words (a).H (a).G (a).payload (a).unit*(a).payload) := by ring
    _ ≤ ratio*(2000*(1+2^((a).k+1)))*(2*DateBill.volumeBits (a).H (a).G (a).payload (a).unit) :=
      Nat.mul_le_mul_left _ live
    _ = _ := by ring

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
