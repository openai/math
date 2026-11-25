import OAI.Computability.NearSquareRoot.CRTControlledFlat
import Mathlib.Data.Nat.Bitwise
import Mathlib.Order.Preorder.Finite

/-! # Numerical coordinates in a flat record stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Packed
open IntegerMultiplication.Strip IntegerMultiplication.Loom

private theorem code_cons_bit (a : Fin 2) (s : Raw 2) :
    code (a :: s) = Nat.bit (title a) (code s) := by
  fin_cases a <;> simp [code, title, Nat.bit_false_apply, Nat.bit_true_apply, Nat.add_comm]

private theorem code_read (s : Raw 2) (j : ℕ) (hj : j < s.length) :
    title (s[j]'hj) = (code s).testBit j := by
  induction s generalizing j with
  | nil => simp at hj
  | cons a s ih =>
    rw [code_cons_bit]
    cases j with
    | zero => rw [Nat.testBit_bit_zero]; rfl
    | succ j =>
      rw [Nat.testBit_bit_succ]
      exact ih j (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hj)

/-- The least-significant-first physical bit selector reads the canonical bit of
the record's array address. -/
theorem prefixBit_number {k : ℕ} (y : Block 2 k) (j : Fin k) :
    prefixBit y j = (number y).testBit j.val :=
  code_read (least y) j.val (by simpa only [length'] using j.isLt)

/-- Physical field order is the increasing sequence of its base-`b` numbers. -/
theorem lineIndex_number {b k : ℕ} [NeZero b] (y : Block b k) :
    ((line b k).index y).val = number y := by
  let s := line b k
  let ord (i : Fin s.count) : Fin s.count :=
    ⟨number (s.follow i), by simpa only [s,lineSize] using number_lt (s.follow i)⟩
  have asc : StrictMono ord := by
    intro i j hij
    exact List.pairwise_iff_getElem.mp (clean b k) _ _ i.isLt j.isLt hij
  have eqn := congrFun asc.eq_id (s.index y)
  have vals := congrArg Fin.val eqn
  simpa only [ord,Series.follow_index,id_eq] using vals.symm

/-- Canonical numeric address of a boxed word, with the physical series index
transported to the actual cardinality. -/
noncomputable def flatAddress (b k : ℕ) : Block b k ≃ Fin (b ^ k) :=
  (line b k).index.trans (finCongr (lineSize b k))

@[simp] theorem flatAddress_val {b k : ℕ} [NeZero b] (y : Block b k) :
    (flatAddress b k y).val = number y := lineIndex_number y

@[simp] theorem prefixBit_address {k : ℕ} (i : Fin (2^k)) (j : Fin k) :
    prefixBit ((flatAddress 2 k).symm i) j = i.val.testBit j.val := by
  rw [prefixBit_number, ← flatAddress_val, Equiv.apply_symm_apply]

theorem line_tab_addresses {A : Type} (b k : ℕ) (f : Fin (b^k) → A) :
    (line b k).tab (f ∘ flatAddress b k) = List.ofFn f := by
  apply List.ext_getElem
  · rw [Series.card,List.length_ofFn,lineSize]
  · intro i hi hj
    have h : i < (line b k).count := by simpa using hi
    rw [(line b k).get (f ∘ flatAddress b k) ⟨i,h⟩ hi]
    simp [flatAddress]

end Controlled

end NearSquareRoot
end Computability
end OAI
