import OAI.Computability.IntegerMultiplication.Bits.Word
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.BigOperators

/-! # Numeric action of an arbitrary physical bit permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open IntegerMultiplication

theorem value_bit (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Bits.value w).testBit i = w[i] := by
  induction w generalizing i with
  | nil => simp at hi
  | cons b w ih =>
    have h : Bits.value (b::w) = Nat.bit b (Bits.value w) := by
      cases b <;> simp [Nat.bit_val, Nat.add_comm]
    rw [h]
    cases i with
    | zero => simp
    | succ i => simpa only [Nat.testBit_bit_succ, List.getElem_cons_succ] using ih i (by simpa using hi)

/-- Packed physical words, with bit zero having weight one. -/
def addressDigits (k : ℕ) : Fin (2^k) ≃ (Fin k → Bool) where
  toFun x i := x.val.testBit i.val
  invFun w := ⟨Bits.value (List.ofFn w), by simpa using Bits.value_lt (List.ofFn w)⟩
  left_inv x := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · rw [value_bit _ _ (by simpa using hi)]
      simp
    · have h : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      have hw := Bits.value_lt (List.ofFn (fun j : Fin k => x.val.testBit j.val))
      rw [List.length_ofFn] at hw
      exact (Nat.testBit_eq_false_of_lt (hw.trans_le h)).trans
        (Nat.testBit_eq_false_of_lt (x.isLt.trans_le h)).symm
  right_inv w := by
    funext i
    simpa using value_bit (List.ofFn w) i.val (by simp)

/-- Send source bit i to physical destination p i, preserving its value. -/
def bitAddress {k : ℕ} (p : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (2^k)) :=
  (addressDigits k).trans ((Equiv.arrowCongr p (Equiv.refl Bool)).trans (addressDigits k).symm)

@[simp] theorem bitAddress_testBit {k : ℕ} (p : Equiv.Perm (Fin k)) (x : Fin (2^k)) (i : Fin k) :
    (bitAddress p x).val.testBit (p i).val = x.val.testBit i.val := by
  change addressDigits k ((addressDigits k).symm _) (p i) = _
  simp [Equiv.arrowCongr]
  rfl

@[simp] theorem bitAddress_symm {k : ℕ} (p : Equiv.Perm (Fin k)) : (bitAddress p).symm = bitAddress p.symm := by
  rfl

@[simp] theorem bitAddress_refl (k : ℕ) : bitAddress (Equiv.refl (Fin k)) = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  apply (addressDigits k).injective
  funext i
  exact bitAddress_testBit (Equiv.refl _) x i

theorem bitAddress_trans {k : ℕ} (p q : Equiv.Perm (Fin k)) :
    bitAddress (p.trans q) = (bitAddress p).trans (bitAddress q) := by
  apply Equiv.ext
  intro x
  apply (addressDigits k).injective
  funext j
  obtain ⟨i,rfl⟩ := (p.trans q).surjective j
  change ((bitAddress (p.trans q)) x).val.testBit ((p.trans q) i).val =
    (bitAddress q (bitAddress p x)).val.testBit (q (p i)).val
  exact (bitAddress_testBit (p.trans q) x i).trans ((bitAddress_testBit q (bitAddress p x) (p i)).trans (bitAddress_testBit p x i)).symm

end BoxFin

end NearSquareRoot
end Computability
end OAI
