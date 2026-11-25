import OAI.Hierarchy.TaggedRadixRecords
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Routing.CompareWord
import Mathlib.Tactic

namespace OAI
/-! # The physical digit wires carry the successive digits of the record key -/

namespace Hierarchy.Tagged.RadixRecord
open ThreeFlat.Routing ExactQuantumFactoring
open scoped Classical

variable {h : ℕ} (z : Bits (width h))

theorem atBit_value (zeroBit : z (zero h) = false) (b : ℕ) :
    z (atBit h b) = (keyValue z).testBit b := by
  have low : (z (kind h)).toNat < 2 := by cases z (kind h) <;> decide
  cases b with
  | zero =>
    simp only [atBit, ite_true, keyValue, Nat.testBit_zero]
    cases z (kind h) <;> simp
  | succ b =>
    have trim : (keyValue z)/2 = (dataTag z).1.val := by
      unfold keyValue
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt low,Nat.zero_add]
    rw [Nat.testBit_succ,trim]
    by_cases ib : b < h
    · rw [show atBit h (b+1)=keyField h ⟨b,ib⟩ by simp [atBit, ib]]
      rw [show (dataTag z).1.val.testBit b = Computability.VPVNP.RAMSerialization.wordBits h (dataTag z).1 ⟨b,ib⟩
        from Computability.VPVNP.LiveHeader.testBit_wordBits (dataTag z).1 (⟨b,ib⟩ : Fin h)]
      simp [dataTag]
    · have top := (dataTag z).1.isLt.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt ib))
      simp [atBit, ib,zeroBit,Nat.testBit_lt_two_pow top]

theorem digit_value (zeroBit : z (zero h) = false) (k pass : ℕ) :
    (addressEquiv k (z ∘ digit h k pass)).val = keyValue z/(2^k)^pass % 2^k := by
  have word : bitsValue (z ∘ digit h k pass) = BitVec.ofNat k (keyValue z/2^(pass*k)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (bitsValue (z ∘ digit h k pass)).getLsbD i = z (atBit h (pass*k+i)) from
      bitsValue_bit _ ⟨i,hi⟩, atBit_value z zeroBit]
    simp [BitVec.getLsbD, Nat.testBit_mod_two_pow, hi, Nat.testBit_div_two_pow, Nat.add_comm]
  change (bitsValue (z ∘ digit h k pass)).toNat = _
  rw [word]
  simp only [BitVec.toNat_ofNat, ← pow_mul, Nat.mul_comm pass k]

end Hierarchy.Tagged.RadixRecord

end OAI
