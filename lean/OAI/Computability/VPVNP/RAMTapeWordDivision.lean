import OAI.Computability.VPVNP.RAMTapeWordSlice
import OAI.Computability.VPVNP.RAMProgram

/-!
# Restoring binary division on a word tape

Process the dividend from its most significant bit to its least significant
bit. At each iteration one subtract-with-borrow scan of width `w+1`
determines the quotient bit. The next remainder is the low `w` bits of the
difference or of the restored candidate. Zero divisor follows the natural
word convention of the RAM instruction table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

/-- Return the quotient bit and new remainder. The high zero on the divisor
allows the left-shifted candidate to use its carry bit. -/
def divideStep (d : List Bool) (b : Bool) (r : List Bool) : Bool × List Bool :=
  let candidate := b :: r
  let trial := subScan false candidate (d ++ [false])
  if trial.2 then (false, candidate.take d.length) else (true, trial.1.take d.length)

theorem divideStep_spec {d r : List Bool} (b : Bool)
    (hlen : r.length = d.length) (hr : value r < value d) :
    let t := divideStep d b r
    t.2.length = d.length ∧ value t.2 < value d ∧
      value d * t.1.toNat + value t.2 = b.toNat + 2 * value r := by
  let x := b :: r
  let y := d ++ [false]
  let trial := subScan false x y
  have hxy : x.length = y.length := by simp [x, y, hlen]
  have ht : trial.1.length = d.length + 1 := by simpa [trial, x, hlen] using length_subScan hxy
  have he := subScan_spec (c := false) hxy
  change value trial.1 + value y + false.toNat = value x + 2 ^ x.length * trial.2.toNat at he
  have hy : value y = value d := by simp [y, value_append, value]
  have hx : value x = b.toNat + 2 * value r := rfl
  have hbl : b.toNat ≤ 1 := by cases b <;> decide
  have htrial := value_lt trial.1
  have hd := value_lt d
  rw [ht] at htrial
  rw [hy, show x.length = d.length + 1 by simp [x, hlen]] at he
  dsimp only
  cases hb : trial.2 with
  | false =>
    simp only [hb, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
    have hv : value trial.1 < value d := by omega
    have hout : divideStep d b r = (true, trial.1.take d.length) := by
      unfold divideStep
      change (if trial.2 then _ else _ : Bool × List Bool) = _
      simp [hb]; rfl
    rw [hout]
    rw [value_take_of_lt (hv.trans hd)]
    exact ⟨by simp [ht], hv, by simp only [Bool.toNat_true, Nat.mul_one]; omega⟩
  | true =>
    simp only [hb, Bool.toNat_false, Nat.add_zero, Bool.toNat_true, Nat.mul_one] at he
    have hv : value x < value d := by omega
    have hout : divideStep d b r = (false, x.take d.length) := by
      unfold divideStep
      change (if trial.2 then _ else _ : Bool × List Bool) = _
      simp [hb]; rfl
    rw [hout]
    have hlen' : d.length ≤ x.length := by simp [x, hlen]
    rw [value_take_of_lt (hv.trans hd)]
    exact ⟨by simp [hlen'], hv, by simp [hx]⟩

/-- The recursive result on the tail is the result on the already consumed
higher-order prefix. Quotient bits are consed in little-endian order. -/
def dividePass (d : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], List.replicate d.length false)
  | b :: xs =>
    let old := dividePass d xs
    let next := divideStep d b old.2
    (next.1 :: old.1, next.2)

theorem dividePass_spec (d xs : List Bool) (hd : 0 < value d) :
    let t := dividePass d xs
    t.1.length = xs.length ∧ t.2.length = d.length ∧ value t.2 < value d ∧
      value d * value t.1 + value t.2 = value xs := by
  induction xs with
  | nil => simp [dividePass, value, hd]
  | cons b xs ih =>
    obtain ⟨hq, hr, hlt, he⟩ := ih
    obtain ⟨hlen, hlt', hstep⟩ := divideStep_spec b hr hlt
    simp only [dividePass, List.length_cons, hq, hlen, hlt', value, true_and, Nat.mul_add]
    rw [← he]
    simp only [Nat.mul_add, Nat.mul_left_comm (value d) 2]
    omega

theorem anyBit_iff (xs : List Bool) : xs.any id = true ↔ 0 < value xs := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih => cases b <;> simp [value, ih]

/-- Both outputs have the width of the input words. For division by zero the
quotient is all zeros and the remainder is the original dividend. -/
def divideWords (x d : List Bool) : List Bool × List Bool :=
  if d.any id then dividePass d x else (List.replicate x.length false, x)

theorem divideWords_spec (x d : List Bool) (hlen : x.length = d.length) :
    let t := divideWords x d
    t.1.length = x.length ∧ t.2.length = x.length ∧
      value t.1 = value x / value d ∧ value t.2 = value x % value d := by
  unfold divideWords
  split
  · rename_i h
    have hd := (anyBit_iff d).mp h
    obtain ⟨hq, hr, hlt, he⟩ := dividePass_spec d x hd
    refine ⟨hq, hr.trans hlen.symm, ?_, ?_⟩
    · rw [← he, Nat.mul_add_div hd, Nat.div_eq_of_lt hlt, Nat.add_zero]
    · rw [← he, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  · rename_i h
    have hd : value d = 0 := by have := (anyBit_iff d).not.mp h; omega
    simp [hd]

open BurstRAM PrivateRAM in
/-- The output bit stacks are the words returned by the RAM's division and
remainder opcodes, including at zero width. -/
theorem divideWords_wordBits {w : ℕ} (x d : Word w) :
    divideWords (wordBits x) (wordBits d) =
      (wordBits (BinaryOp.div.eval x d), wordBits (BinaryOp.mod.eval x d)) := by
  obtain ⟨hq, hr, hdiv, hmod⟩ := divideWords_spec (wordBits x) (wordBits d) (by simp)
  simp only [value_wordBits] at hdiv hmod
  have hd : x.val / d.val < 2 ^ w := (Nat.div_le_self ..).trans_lt x.isLt
  have hm : x.val % d.val < 2 ^ w := (Nat.mod_le ..).trans_lt x.isLt
  apply Prod.ext
  · apply eq_of_length_value (by simpa using hq)
    simpa [value_wordBits, BinaryOp.eval, Fin.ofNat, Nat.mod_eq_of_lt hd] using hdiv
  · apply eq_of_length_value (by simpa using hr)
    simpa [value_wordBits, BinaryOp.eval, Fin.ofNat, Nat.mod_eq_of_lt hm] using hmod

end TapeWord

end VPVNP
end Computability
end OAI
