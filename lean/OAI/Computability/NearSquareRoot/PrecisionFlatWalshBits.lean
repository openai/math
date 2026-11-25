import OAI.Computability.NearSquareRoot.SynchronizedPhysicalFiber
import Mathlib.Data.Nat.Bitwise

/-! # A butterfly partner in the packed Walsh address space -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshInteger

variable {k : ℕ}

/-- Toggle the bit selecting one of the two inputs to a butterfly. -/
def flip (p : Fin k) (x : Fin (2^k)) : Fin (2^k) :=
  ⟨(x.val ^^^ 2^p.val) % 2^k, Nat.mod_lt _ (by positivity)⟩

theorem testBit_flip (p : Fin k) (x : Fin (2^k)) (q : Fin k) :
    (flip p x).val.testBit q.val =
      if q = p then !(x.val.testBit p.val) else x.val.testBit q.val := by
  simp only [flip, Nat.testBit_mod_two_pow, decide_eq_true q.isLt, Bool.true_and, Nat.testBit_xor]
  by_cases h : q = p
  · subst q
    simp
  · have hv : p.val ≠ q.val := fun he => h (Fin.ext he.symm)
    simp [h, Nat.testBit_two_pow_of_ne hv]

theorem offBits_empty_iff (x y : Fin (2^k)) : BoxFin.offBits ∅ x y ↔ x = y := by
  constructor
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact h ⟨i, hi⟩ (by simp)
    · have hpow : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hpow),
        Nat.testBit_eq_false_of_lt (y.isLt.trans_le hpow)]
  · rintro rfl q _
    rfl

end FlatWalshInteger

end NearSquareRoot
end Computability
end OAI
