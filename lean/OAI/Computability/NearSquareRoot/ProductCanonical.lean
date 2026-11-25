import OAI.Computability.IntegerMultiplication.Lea.Assembly

/-! # Uniqueness of the full-width, most-significant-first product word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductRecovery

open IntegerMultiplication

/-- The bit-level postcondition in the independent machine specification singles
out precisely the canonical padded word of the P192 multiplication interface. -/
theorem product_postcondition_iff {n : ℕ} (x y z : List Bool) (hx : x.length = n) (hy : y.length = n) :
    z.length = 2*n ∧ bitValue z = bitValue x * bitValue y ↔ z = Lea.answer (x,y) := by
  have both : x.length = y.length := hx.trans hy.symm
  have hlen := Lea.date_length (x,y)
  have hval := Lea.value_answer (j := (x,y)) both
  change (Lea.answer (x,y)).length = 2*x.length at hlen
  change bitValue (Lea.answer (x,y)) = bitValue x * bitValue y at hval
  rw [hx] at hlen
  constructor
  · rintro ⟨hl,hv⟩
    apply List.reverse_inj.mp
    apply Bits.word_inject
    · simpa only [List.length_reverse] using hl.trans hlen.symm
    · simpa only [← endianness] using hv.trans hval.symm
  · rintro rfl
    exact ⟨hlen, hval⟩

end ProductRecovery

end NearSquareRoot
end Computability
end OAI
