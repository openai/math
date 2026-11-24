import OAI.Computability.VPVNP.RAMTapeWord
import Mathlib.Data.Nat.ModEq

/-!
# Multiplication on fixed-width bit tapes

In each round the multiplier supplies its next low bit. A single synchronous
scan of the other two words shifts the multiplicand and adds its selected
bits to the accumulator. Discarding the last shifted bit and the last carry
implements the word RAM's multiplication modulo its word size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

/-- Emit the previous multiplicand bit and the current accumulator sum bit.
The finite control retains the shifted-out bit and the adder carry. -/
def mulScan (use : Bool) : Bool → Bool → List Bool → List Bool → List Bool × List Bool
  | carry, prev, b :: xs, d :: ds =>
    let sum := addBit carry (use && b) d
    let out := mulScan use sum.2 b xs ds
    (prev :: out.1, sum.1 :: out.2)
  | _, _, _, _ => ([], [])

/-- Start one shift-and-add scan with zero incoming shift bit and carry. -/
def mulRound (use : Bool) (x acc : List Bool) : List Bool × List Bool :=
  mulScan use false false x acc

/-- Consume the multiplier from low to high, retaining the two output words
between rounds. -/
def mulFold : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | use :: bits, x, acc =>
    let out := mulRound use x acc
    mulFold bits out.1 out.2

theorem length_mulScan (use carry prev : Bool) {x acc : List Bool}
    (hlen : acc.length = x.length) :
    (mulScan use carry prev x acc).1.length = x.length ∧
      (mulScan use carry prev x acc).2.length = x.length := by
  induction x generalizing carry prev acc with
  | nil => cases acc <;> simp [mulScan]
  | cons b xs ih =>
    cases acc with
    | nil => simp at hlen
    | cons d ds =>
      obtain ⟨hx, ha⟩ := ih (addBit carry (use && b) d).2 b (Nat.succ.inj hlen)
      simp [mulScan, hx, ha]

theorem length_mulRound (use : Bool) {x acc : List Bool} (hlen : acc.length = x.length) :
    (mulRound use x acc).1.length = x.length ∧ (mulRound use x acc).2.length = x.length :=
  length_mulScan use false false hlen

theorem length_mulFold (bits : List Bool) {x acc : List Bool} (hlen : acc.length = x.length) :
    (mulFold bits x acc).length = x.length := by
  induction bits generalizing x acc with
  | nil => exact hlen
  | cons b bits ih =>
    obtain ⟨hx, ha⟩ := length_mulRound b hlen
    exact (ih (ha.trans hx.symm)).trans hx

/-- Each finite scan discards whole multiples of the word modulus. -/
private theorem mulScan_overflow (use carry prev : Bool) {x acc : List Bool}
    (hlen : acc.length = x.length) :
    ∃ shiftOverflow addOverflow : ℕ,
      2 * value x + prev.toNat =
        value (mulScan use carry prev x acc).1 + 2 ^ x.length * shiftOverflow ∧
      value acc + use.toNat * value x + carry.toNat =
        value (mulScan use carry prev x acc).2 + 2 ^ x.length * addOverflow := by
  induction x generalizing acc carry prev with
  | nil =>
    cases acc with
    | nil => exact ⟨prev.toNat, carry.toNat, by simp [mulScan, value]⟩
    | cons => simp at hlen
  | cons b xs ih =>
    cases acc with
    | nil => simp at hlen
    | cons d ds =>
      let sum := addBit carry (use && b) d
      obtain ⟨shiftOverflow, addOverflow, hx, ha⟩ := ih sum.2 b (Nat.succ.inj hlen)
      have hbit : d.toNat + use.toNat * b.toNat + carry.toNat =
          sum.1.toNat + 2 * sum.2.toNat := by
        cases use <;> cases b <;> cases d <;> cases carry <;> decide
      refine ⟨shiftOverflow, addOverflow, ?_, ?_⟩
      · change 2 * (b.toNat + 2 * value xs) + prev.toNat =
          prev.toNat + 2 * value (mulScan use sum.2 b xs ds).1 +
            2 ^ (xs.length + 1) * shiftOverflow
        rw [pow_succ, Nat.mul_right_comm _ 2 shiftOverflow]
        omega
      · change (d.toNat + 2 * value ds) + use.toNat * (b.toNat + 2 * value xs) +
          carry.toNat = sum.1.toNat + 2 * value (mulScan use sum.2 b xs ds).2 +
            2 ^ (xs.length + 1) * addOverflow
        rw [pow_succ, Nat.mul_right_comm _ 2 addOverflow, Nat.mul_add,
          ← Nat.mul_assoc use.toNat 2, Nat.mul_right_comm use.toNat 2]
        omega

theorem value_mulRound (use : Bool) {x acc : List Bool} (hlen : acc.length = x.length) :
    value (mulRound use x acc).1 = (2 * value x) % 2 ^ x.length ∧
      value (mulRound use x acc).2 = (value acc + use.toNat * value x) % 2 ^ x.length := by
  obtain ⟨sx, sa, hx, ha⟩ := mulScan_overflow use false false hlen
  simp only [Bool.toNat_false, Nat.add_zero] at hx ha
  obtain ⟨hxl, hal⟩ := length_mulRound use hlen
  have bx := value_lt (mulRound use x acc).1
  have ba := value_lt (mulRound use x acc).2
  rw [hxl] at bx
  rw [hal] at ba
  unfold mulRound at bx ba
  rw [hx, ha, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt bx, Nat.mod_eq_of_lt ba]
  exact ⟨rfl, rfl⟩

/-- The full shift-and-add computation, including an arbitrary initial
accumulator, is the low word of the mathematical product plus that accumulator. -/
theorem value_mulFold (bits : List Bool) {x acc : List Bool} (hlen : acc.length = x.length) :
    value (mulFold bits x acc) = (value acc + value x * value bits) % 2 ^ x.length := by
  induction bits generalizing x acc with
  | nil =>
    have hb := value_lt acc
    rw [hlen] at hb
    simp [mulFold, value, Nat.mod_eq_of_lt hb]
  | cons b bits ih =>
    obtain ⟨hx, ha⟩ := length_mulRound b hlen
    obtain ⟨hvx, hva⟩ := value_mulRound b hlen
    rw [mulFold, ih (ha.trans hx.symm), hx, hvx, hva, value]
    have h := (Nat.mod_modEq (value acc + b.toNat * value x) (2 ^ x.length)).add
      ((Nat.mod_modEq (2 * value x) (2 ^ x.length)).mul_right (value bits))
    calc
      _ = (value acc + b.toNat * value x + (2 * value x) * value bits) % 2 ^ x.length := h
      _ = _ := by congr 1; ring

private theorem value_replicate_false (w : ℕ) : value (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, value, ih]

/-- Starting with a zero tape produces the canonical bit string of the
word product, including when the word multiplication wraps around. -/
theorem mulFold_wordBits {w : ℕ} (a b : BurstRAM.Word w) :
    mulFold (BurstRAM.wordBits b) (BurstRAM.wordBits a) (List.replicate w false) =
      BurstRAM.wordBits (a * b) := by
  have hlen : (List.replicate w false).length = (BurstRAM.wordBits a).length := by simp
  apply eq_of_length_value
  · simp [length_mulFold _ hlen]
  · rw [value_mulFold _ hlen, value_replicate_false, Nat.zero_add, value_wordBits,
      value_wordBits, value_wordBits, BurstRAM.length_wordBits]
    rfl

end TapeWord

end VPVNP
end Computability
end OAI
