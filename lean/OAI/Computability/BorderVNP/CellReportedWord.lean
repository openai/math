import OAI.Computability.BorderVNP.CellSparseFactorCode
import Mathlib.Data.Nat.BinaryRec

/-! # Verifying a binary subtotal against the final one-hot prefix row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro
open Profile (data)

private theorem word_cons (b : ℕ → Bool) (i : ℕ) (is : List ℕ) :
    word b (i::is) = Nat.bit (b i) (word b is) := by
  cases h : b i <;> simp [word, Nat.bit, h, Nat.add_comm]

/-- A binary subtotal fits in its declared number of bits. -/
theorem word_bound (b : ℕ → Bool) (is : List ℕ) : word b is < 2 ^ is.length := by
  induction is with
  | nil => simp [word]
  | cons i is ih =>
    simp only [List.length_cons, Nat.pow_succ, word]
    split <;> omega

/-- The digit at each valid index is exactly the named bit in the original bank. -/
theorem word_digit (b : ℕ → Bool) (is : List ℕ) (i : ℕ) (h : i < is.length) :
    (word b is).testBit i = b is[i] := by
  induction is generalizing i with
  | nil => simp at h
  | cons a is ih =>
    rw [word_cons]
    cases i with
    | zero => simp
    | succ i => simpa [Nat.testBit_bit_succ] using ih i (by simpa using h)

/-- Check every supplied digit against the corresponding bit of the candidate integer. -/
def digitChecks (off : ℕ) (bits : List ℕ) (k : NatExpr) : Term :=
  Term.all (bits.zipIdx.map fun bi =>
    (Term.wire (.lit (off+bi.1))).equal (.paramBit k (.lit bi.2)))

/-- Provided the candidate fits the binary field, the checks are equivalent to
equality with the proposed subtotal. -/
theorem digitChecks_correct (off : ℕ) (bits : List ℕ) (k : NatExpr) (e : List ℕ)
    (b : ℕ → Bool) (hk : k.eval e < 2 ^ bits.length) :
    (digitChecks off bits k).eval e b = true ↔ word (data off b) bits = k.eval e := by
  simp only [digitChecks, Term.eval_all, List.all_eq_true, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Term.eval_equal, Term.eval, NatExpr.eval]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < bits.length
    · rw [word_digit _ _ _ hi]
      exact of_decide_eq_true (h (bits[i], i) (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)))
    · have hp : 2 ^ bits.length ≤ (2:ℕ)^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((word_bound ..).trans_le hp), Nat.testBit_lt_two_pow (hk.trans_le hp)]
  · intro h
    rintro ⟨a,i⟩ hm
    have hx := List.mem_zipIdx_iff_getElem?.mp hm
    have hi : i < bits.length := by
      by_contra! hg
      simp [List.getElem?_eq_none_iff.mpr hg] at hx
    have ha : bits[i] = a := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hx)
    apply decide_eq_true
    change b (off+a) = (k.eval e).testBit i
    rw [← h, word_digit _ _ _ hi, ha]
    rfl

/-- If candidate `k` is marked, the reported binary count must equal `k`.
Counts beyond the range of the reported field are rejected. -/
def finishCount (base off cap : ℕ) (bits : List ℕ) : Stmt :=
  let k := NatExpr.index 0
  let flag := Prefix.flagTerm base cap (.lit cap) k
  .loop (.lit (cap+1)) (.ifEq (.sub k (.lit (min cap (2^bits.length-1)))) (.lit 0)
    (flag.implies (digitChecks off bits k)).guard flag.not.guard)

/-- The final one-hot row can contain a true bit only at the reported count. -/
theorem finishCount_checks (base off cap : ℕ) (bits : List ℕ) (e : List ℕ) :
    Profile.Tests (finishCount base off cap bits) e (fun b =>
      ∀ k ≤ cap, b (Prefix.address base cap cap k) = true → word (data off b) bits = k) := by
  apply Prefix.checks_congr (loop_checks (.lit (cap+1)) _ e (fun k b =>
    decide (b (Prefix.address base cap cap k) = true → word (data off b) bits = k)) ?_)
  · intro b
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range, NatExpr.eval, Nat.lt_succ_iff, decide_eq_true_eq]
  · intro k hk ops st v
    have hk' : k ≤ cap := Nat.le_of_lt_succ hk
    by_cases h : k < 2 ^ bits.length
    · have hle : k - min cap (2 ^ bits.length - 1) = 0 := by omega
      simp only [Stmt.expand, NatExpr.eval, List.getD_cons_zero, hle, ite_true, Term.value_guard]
      have hd := digitChecks_correct off bits (.index 0) (k::e) (lookup v) h
      have he : (Term.implies (Prefix.flagTerm base cap (.lit cap) (.index 0))
            (digitChecks off bits (.index 0))).eval (k::e) (lookup v) =
          decide (lookup v (Prefix.address base cap cap k) = true → word (data off (lookup v)) bits = k) := by
        apply Bool.eq_iff_iff.mpr
        cases hb : lookup v (Prefix.address base cap cap k) <;>
          simp [Term.implies, Term.eval, Prefix.flagTerm, Prefix.address, NatExpr.eval] at hb ⊢ <;>
          simp [hb, hd, NatExpr.eval]
      rw [he]
    · have hne : k - min cap (2 ^ bits.length - 1) ≠ 0 := by
        have : 0 < (2:ℕ)^bits.length := Nat.pow_pos (by decide)
        omega
      have hbad : word (data off (lookup v)) bits ≠ k := by
        have := word_bound (data off (lookup v)) bits
        omega
      simp only [Stmt.expand, NatExpr.eval, List.getD_cons_zero, hne, ite_false, Term.value_guard]
      simp [Term.eval, Prefix.flagTerm, Prefix.address, NatExpr.eval, hbad]

end CellSparse

end BorderVNP
end Computability
end OAI
