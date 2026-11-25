import OAI.Computability.BorderVNP.ParseBatchSortCompare

/-! # Binary address arithmetic for parse-table records

Words are most significant bit first. The carry expression for any one position reads
each lower position with constant overhead, even when the Boolean expressions are
compiled as trees. An overflowing sum or difference is computed modulo the word size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchSort

open VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ : Type*} {w : ℕ}

/-- Unsigned numerical interpretation of a word of Boolean formulas. -/
def wordValue (z : σ → Bool) (a : Fin w → Expr σ) : ℕ := value (fun i => (a i).eval z)

private def xorBit (a b : Expr σ) : Expr σ := .and (.or a b) (.not (.and a b))

private def nextCarry (a b c : Expr σ) : Expr σ :=
  .or (.and a b) (.and (.or a b) c)

private theorem bitSum (z : σ → Bool) (a b c : Expr σ) :
    2 * ((nextCarry a b c).eval z).toNat + ((xorBit (xorBit a b) c).eval z).toNat =
      (a.eval z).toNat + (b.eval z).toNat + (c.eval z).toNat := by
  cases ha : a.eval z <;> cases hb : b.eval z <;> cases hc : c.eval z <;>
    simp [nextCarry, xorBit, StatementCircuit.Expr.eval, ha, hb, hc]

/-- Carry out of a pair of words with a specified initial carry. -/
def carryWord (cin : Bool) : {w : ℕ} → (Fin w → Expr σ) → (Fin w → Expr σ) → Expr σ
  | 0, _, _ => .const cin
  | _+1, a, b => nextCarry (a 0) (b 0) (carryWord cin (fun i => a i.succ) (fun i => b i.succ))

/-- The low bits of a sum with a specified carry into the least significant bit. -/
def sumWord (cin : Bool) : {w : ℕ} → (Fin w → Expr σ) → (Fin w → Expr σ) → Fin w → Expr σ
  | 0, _, _ => fun i => i.elim0
  | _+1, a, b =>
    let atail := fun i => a i.succ
    let btail := fun i => b i.succ
    Fin.cons (xorBit (xorBit (a 0) (b 0)) (carryWord cin atail btail))
      (sumWord cin atail btail)

/-- Including the carry bit gives the exact sum of the two input values. -/
theorem sumWord_value_carry (z : σ → Bool) (cin : Bool) (a b : Fin w → Expr σ) :
    ((carryWord cin a b).eval z).toNat * 2^w + wordValue z (sumWord cin a b) =
      wordValue z a + wordValue z b + cin.toNat := by
  induction w with
  | zero => simp [carryWord, wordValue, value, StatementCircuit.Expr.eval]
  | succ w ih =>
    let atail := fun (i : Fin w) => a i.succ
    let btail := fun (i : Fin w) => b i.succ
    let c := carryWord cin atail btail
    have ht := ih atail btail
    change ((nextCarry (a 0) (b 0) c).eval z).toNat * 2^(w+1) +
      (((xorBit (xorBit (a 0) (b 0)) c).eval z).toNat * 2^w +
        wordValue z (sumWord cin atail btail)) =
      ((a 0).eval z).toNat * 2^w + wordValue z atail +
        (((b 0).eval z).toNat * 2^w + wordValue z btail) + cin.toNat
    calc
      _ = (2 * ((nextCarry (a 0) (b 0) c).eval z).toNat +
        ((xorBit (xorBit (a 0) (b 0)) c).eval z).toNat) * 2^w +
          wordValue z (sumWord cin atail btail) := by rw [pow_succ]; ring
      _ = ((a 0).eval z).toNat * 2^w + ((b 0).eval z).toNat * 2^w +
          ((c.eval z).toNat * 2^w + wordValue z (sumWord cin atail btail)) := by
        rw [bitSum]
        ring
      _ = _ := by dsimp only [c]; rw [ht]; ring

/-- Addition of two unsigned binary records. -/
def addWord (a b : Fin w → Expr σ) : Fin w → Expr σ := sumWord false a b

/-- The value of a sum when it fits in the record width. -/
theorem addWord_value (z : σ → Bool) (a b : Fin w → Expr σ)
    (h : wordValue z a + wordValue z b < 2^w) :
    wordValue z (addWord a b) = wordValue z a + wordValue z b := by
  have hsum := sumWord_value_carry z false a b
  cases hc : (carryWord false a b).eval z <;> simp [hc, addWord] at hsum ⊢ <;> omega

/-- Unsigned subtraction in two's complement, including the final carry into the low bit. -/
def subWord (a b : Fin w → Expr σ) : Fin w → Expr σ :=
  sumWord true a (fun i => .not (b i))

private theorem complement_value (z : σ → Bool) (a : Fin w → Expr σ) :
    wordValue z (fun i => StatementCircuit.Expr.not (a i)) + wordValue z a + 1 = 2^w := by
  induction w with
  | zero => simp [wordValue, value]
  | succ w ih =>
    have ht := ih (fun i => a i.succ)
    cases h : (a 0).eval z <;>
      simp only [wordValue, value, StatementCircuit.Expr.eval, h, Bool.not_true, Bool.not_false,
        Bool.toNat_true, Bool.toNat_false, one_mul, zero_mul, zero_add, pow_succ] at ht ⊢ <;> omega

/-- Exact value of subtraction for a non-underflowing pair of unsigned operands. -/
theorem subWord_value (z : σ → Bool) (a b : Fin w → Expr σ) (h : wordValue z b ≤ wordValue z a) :
    wordValue z (subWord a b) = wordValue z a - wordValue z b := by
  let neg := fun i => StatementCircuit.Expr.not (b i)
  have hc := complement_value z b
  have hs := sumWord_value_carry z true a neg
  have hl := value_lt (fun i => ((sumWord true a neg) i).eval z)
  change wordValue z (sumWord true a neg) < 2^w at hl
  change wordValue z neg + wordValue z b + 1 = 2^w at hc
  change wordValue z (sumWord true a neg) = _
  cases he : (carryWord true a neg).eval z <;> simp only [he, Bool.toNat_false, Bool.toNat_true,
    zero_mul, one_mul, zero_add] at hs <;> omega

/-- Increment an unsigned record using one carry into an all-zero second operand. -/
def incWord (a : Fin w → Expr σ) : Fin w → Expr σ := sumWord true a (fun _ => .const false)

private theorem zero_value (z : σ → Bool) : wordValue z (fun _ : Fin w => .const false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa [wordValue, value, StatementCircuit.Expr.eval] using ih

/-- Increment computes successor whenever the result fits. -/
theorem incWord_value (z : σ → Bool) (a : Fin w → Expr σ) (h : wordValue z a + 1 < 2^w) :
    wordValue z (incWord a) = wordValue z a + 1 := by
  have hs := sumWord_value_carry z true a (fun _ => .const false)
  rw [zero_value] at hs
  cases he : (carryWord true a (fun _ => .const false)).eval z <;>
    simp only [he, Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add, add_zero] at hs
  all_goals dsimp only [incWord]; omega

private def firstBit : {w : ℕ} → (Fin w → Expr σ) → Expr σ
  | 0, _ => .const false
  | _+1, a => a 0

/-- Shift left by one. This is just rewiring followed by a zero in the low position. -/
def doubleWord : {w : ℕ} → (Fin w → Expr σ) → Fin w → Expr σ
  | 0, _ => fun i => i.elim0
  | _+1, a =>
    let tail := fun i => a i.succ
    Fin.cons (firstBit tail) (doubleWord tail)

private theorem double_value_carry (z : σ → Bool) (a : Fin w → Expr σ) :
    ((firstBit a).eval z).toNat * 2^w + wordValue z (doubleWord a) = 2 * wordValue z a := by
  induction w with
  | zero => rfl
  | succ w ih =>
    have ht := ih (fun i => a i.succ)
    change ((a 0).eval z).toNat * 2^(w+1) + (((firstBit (fun i => a i.succ)).eval z).toNat * 2^w +
      wordValue z (doubleWord fun i => a i.succ)) =
      2 * (((a 0).eval z).toNat * 2^w + wordValue z (fun i => a i.succ))
    rw [ht, pow_succ]
    ring

/-- Doubling is exact when its high bit stays within the word. -/
theorem doubleWord_value (z : σ → Bool) (a : Fin w → Expr σ) (h : 2 * wordValue z a < 2^w) :
    wordValue z (doubleWord a) = 2 * wordValue z a := by
  have hd := double_value_carry z a
  cases he : (firstBit a).eval z <;> simp [he] at hd <;> omega

/-- The carry grows linearly with the word width when each input bit has bounded cost. -/
theorem carryWord_size_le (cin : Bool) (a b : Fin w → Expr σ) (D : ℕ)
    (ha : ∀ i, (a i).size ≤ D) (hb : ∀ i, (b i).size ≤ D) :
    (carryWord cin a b).size ≤ 1 + (4*D+4)*w := by
  induction w with
  | zero => simp [carryWord, StatementCircuit.Expr.size]
  | succ w ih =>
    have ht := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => ha i.succ) (fun i => hb i.succ)
    have := ha 0
    have := hb 0
    simp only [carryWord, nextCarry, StatementCircuit.Expr.size, Nat.mul_succ]
    omega

/-- Each output bit has linear expression cost in the width. -/
theorem sumWord_size_le (cin : Bool) (a b : Fin w → Expr σ) (D : ℕ)
    (ha : ∀ i, (a i).size ≤ D) (hb : ∀ i, (b i).size ≤ D) (i : Fin w) :
    (sumWord cin a b i).size ≤ (8*D+8)*w + 8*D + 14 := by
  induction w with
  | zero => exact i.elim0
  | succ w ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have ht := carryWord_size_le cin (fun i => a i.succ) (fun i => b i.succ) D
        (fun i => ha i.succ) (fun i => hb i.succ)
      have := ha 0
      have := hb 0
      simp only [sumWord, Fin.cons_zero, xorBit, StatementCircuit.Expr.size, Nat.mul_succ]
      nlinarith
    · have ht := ih (fun i => a i.succ) (fun i => b i.succ)
        (fun i => ha i.succ) (fun i => hb i.succ) j
      simp only [sumWord, Fin.cons_succ, Nat.mul_succ]
      omega

/-- Subtraction's complement costs one extra NOT per input-bit occurrence. -/
theorem subWord_size_le (a b : Fin w → Expr σ) (D : ℕ)
    (ha : ∀ i, (a i).size ≤ D) (hb : ∀ i, (b i).size ≤ D) (i : Fin w) :
    (subWord a b i).size ≤ (8*(D+1)+8)*w + 8*(D+1) + 14 :=
  sumWord_size_le true a (fun j => .not (b j)) (D+1) (fun j => (ha j).trans (Nat.le_succ _))
    (fun j => Nat.succ_le_succ (hb j)) i

/-- Shifting only selects existing input bits or a single zero constant. -/
theorem doubleWord_size_le (a : Fin w → Expr σ) (D : ℕ)
    (ha : ∀ i, (a i).size ≤ D) (i : Fin w) : (doubleWord a i).size ≤ max D 1 := by
  induction w with
  | zero => exact i.elim0
  | succ w ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [doubleWord, Fin.cons_zero]
      cases w with
      | zero => exact Nat.le_max_right _ _
      | succ w => exact (ha (Fin.succ 0)).trans (Nat.le_max_left _ _)
    · simpa only [doubleWord, Fin.cons_succ] using ih (fun i => a i.succ) (fun i => ha i.succ) j

end ParseBatchSort

end BorderVNP
end Computability
end OAI
