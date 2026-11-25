import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.TraceSuffixOracle
import OAI.ThreeFlat.RAM.PhysicalRawTape

namespace OAI
/-! # Exact default record after the finite table of a prepared H header -/

namespace ThreeFlat.RAM.TraceSuffixOracle

open Computability.VPVNP.BurstRAM Diagonal.TraceAddressRecord
open scoped Fin.CommRing

variable {F : Type*} [CommSemiring F] {q w : ℕ}

theorem default_field (j : Fin 11) : TraceAddressReader.fields ({} : Record) j =
    if j.val=3 then 1 else 0 := by fin_cases j <;> rfl

omit [CommSemiring F] in
theorem default_word (N : BitNetwork F q) (code : FieldCode F w) (keys : Fin q → Record) (i : ℕ)
    (after : FixedTraceImage.count N≤ i) :
    FixedTraceImage.word N code keys i = (if i%11=3 then 1 else 0 : ℕ) := by
  unfold FixedTraceImage.count at after
  have start : 11*N.cells≤ i := by omega
  have past : ¬(i-11*N.cells)/11<q := by omega
  have same : (i-11*N.cells)%11=i%11 := by omega
  simp only [FixedTraceImage.word,Nat.not_lt_of_ge start,ite_false,TraceTemplate.getRecord,
    dite_eq_right past,default_field,same]

omit [CommSemiring F] in
theorem tail_bit (N : BitNetwork F q) (code : FieldCode F w) (keys : Fin q → Record) (a : ℕ)
    (hw : 0<w) (after : w*FixedTraceImage.count N≤a) :
    ((FixedTraceImage.bits (FixedTraceImage.word N code keys) a)).toNat=tailBit w a := by
  have far : FixedTraceImage.count N≤a/w :=
    (Nat.le_div_iff_mul_le hw).2 (by simpa only [Nat.mul_comm] using after)
  have hi := Nat.mod_lt a hw
  have cap : 1<2^w := Nat.one_lt_two_pow hw.ne'
  rw [FixedTraceImage.bits,default_word N code keys _ far]
  by_cases field : a/w%11=3 <;> by_cases last : a%w=w-1
  · simp [tailBit,field,last,hw]
  · have pos : 0<w-1-a%w := by omega
    have ne : w-1-a%w≠0 := by omega
    have off : (1 : ℕ).testBit (w-1-a%w)=false := by
      cases h : (1 : ℕ).testBit (w-1-a%w) with
      | false => rfl
      | true => exact False.elim (ne (Nat.testBit_one_eq_true_iff_self_eq_zero.mp h))
    simp [tailBit,field,last,off]
  · simp [tailBit,field]
  · simp [tailBit,field]

end ThreeFlat.RAM.TraceSuffixOracle

end OAI
