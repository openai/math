import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.BooleanVector
import OAI.Computability.VPVNP.RAMProgram

namespace OAI
/-! # Boolean networks for the bitwise RAM opcodes

A public set of `w` possible shift distances is decoded by tests on the
second input word. A shifted output bit is a disjunction of the enabled
source bits. Larger shifts therefore return the zero word.
-/

namespace ThreeFlat.Diagonal.TraceBitwiseOps

open ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork Computability.VPVNP.BurstRAM
open Computability.VPVNP.BurstRAM.PrivateRAM

inductive Op where
  | bitAnd | bitOr | bitXor | shiftLeft | shiftRight

def Op.toBinary : Op → BinaryOp
  | .bitAnd => .bitAnd
  | .bitOr => .bitOr
  | .bitXor => .bitXor
  | .shiftLeft => .shiftLeft
  | .shiftRight => .shiftRight

private abbrev Net (w : ℕ) := BooleanNetwork (w+w) 1
private def lhs {w : ℕ} (i : Fin w) : Net w := bit (i.castAdd w)
private def rhs {w : ℕ} (i : Fin w) : Net w := bit (Fin.natAdd w i)
private abbrev pins {w : ℕ} (x y : Word w) :=
  Fin.append (fun j : Fin w => x.val.testBit j.val) (fun j : Fin w => y.val.testBit j.val)

@[simp] private theorem lhs_eval {w : ℕ} (i : Fin w) (x y : Word w) :
    (lhs i).eval (pins x y) 0 = x.val.testBit i.val := by simp [lhs, pins]
@[simp] private theorem rhs_eval {w : ℕ} (i : Fin w) (x y : Word w) :
    (rhs i).eval (pins x y) 0 = y.val.testBit i.val := by
  rw [rhs, eval_bit]
  exact Fin.append_right (fun j : Fin w => x.val.testBit j.val)
    (fun j : Fin w => y.val.testBit j.val) i

private def literal {w : ℕ} (s j : Fin w) : Net w :=
  if s.val.testBit j.val then rhs j else (rhs j).bnot

private theorem literal_true {w : ℕ} (s j : Fin w) (x y : Word w) :
    (literal s j).eval (pins x y) 0 = true ↔ y.val.testBit j.val = s.val.testBit j.val := by
  cases hs : s.val.testBit j.val <;> simp [literal, hs]

private def distanceTest {w : ℕ} (s : Fin w) : Net w := all (List.ofFn (literal s))

private theorem distance_true {w : ℕ} (s : Fin w) (x y : Word w) :
    (distanceTest s).eval (pins x y) 0 = true ↔ y.val = s.val := by
  rw [distanceTest, all_eval]
  have eqBits : (∀ c ∈ List.ofFn (literal s), c.eval (pins x y) 0 = true) ↔
      ∀ j : Fin w, y.val.testBit j.val = s.val.testBit j.val := by
    constructor
    · intro h j
      exact (literal_true s j x y).mp (h _ (List.mem_ofFn.mpr ⟨j,rfl⟩))
    · intro h c hc
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
      exact (literal_true s j x y).mpr (h j)
  rw [eqBits]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < w
    · exact h ⟨i,hi⟩
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
      rw [Nat.testBit_lt_two_pow (y.isLt.trans_le hp),
        Nat.testBit_lt_two_pow ((s.isLt.trans (Nat.lt_two_pow_self (n := w))).trans_le hp)]
  · rintro h j
    rw [h]

private theorem distance_count {w : ℕ} (s : Fin w) :
    (distanceTest s).net.count ≤ 2*w+1 := by
  have H := all_count (List.ofFn (literal s)) (c := 1) (by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    cases hs : s.val.testBit j.val
    · rw [show literal s j = (rhs j).bnot by simp [literal, hs]]
      simp [rhs]
    · rw [show literal s j = rhs j by simp [literal, hs]]
      simp [rhs])
  simpa [distanceTest, Nat.mul_comm] using H

private def shiftedBit {w : ℕ} (left : Bool) (s j : Fin w) : Net w :=
  if left then
    if s.val ≤ j.val then lhs ⟨j.val-s.val, by omega⟩ else constant false
  else if h : s.val+j.val < w then lhs ⟨s.val+j.val,h⟩ else constant false

private theorem shiftedBit_eval {w : ℕ} (left : Bool) (s j : Fin w) (x y : Word w) :
    (shiftedBit left s j).eval (pins x y) 0 =
      (if left then x.val <<< s.val else x.val >>> s.val).testBit j.val := by
  cases left
  · by_cases h : s.val + j.val < w
    · simp [shiftedBit, h]
    · have hn := Nat.testBit_lt_two_pow (i := s.val + j.val)
        (x.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt h)))
      simp [shiftedBit, h, hn]
  · by_cases h : s.val ≤ j.val <;> simp [shiftedBit, h]

private theorem shiftedBit_count {w : ℕ} (left : Bool) (s j : Fin w) :
    (shiftedBit left s j).net.count ≤ 1 := by
  cases left
  · by_cases h : s.val+j.val < w
    · rw [show shiftedBit false s j = lhs ⟨s.val+j.val,h⟩ by simp [shiftedBit, h]]
      simp [lhs]
    · rw [show shiftedBit false s j = constant false by simp [shiftedBit, h]]
      simp
  · by_cases h : s.val ≤ j.val
    · rw [show shiftedBit true s j = lhs ⟨j.val-s.val,by omega⟩ by simp [shiftedBit, h]]
      simp [lhs]
    · rw [show shiftedBit true s j = constant false by simp [shiftedBit, h]]
      simp

private def shift {w : ℕ} (left : Bool) (j : Fin w) : Net w :=
  any (List.ofFn fun s : Fin w => (distanceTest s).band (shiftedBit left s j))

private theorem shift_true {w : ℕ} (left : Bool) (j : Fin w) (x y : Word w) :
    (shift left j).eval (pins x y) 0 = true ↔
      y.val < w ∧ (if left then x.val <<< y.val else x.val >>> y.val).testBit j.val = true := by
  simp only [shift, any_eval, List.mem_ofFn, exists_exists_eq_and, eval_band,
    Bool.and_eq_true, distance_true, shiftedBit_eval]
  constructor
  · rintro ⟨s, hs, hb⟩
    exact ⟨hs ▸ s.isLt, hs ▸ hb⟩
  · rintro ⟨hy,hb⟩
    exact ⟨⟨y.val,hy⟩,rfl,hb⟩

private theorem shift_count {w : ℕ} (left : Bool) (j : Fin w) :
    (shift left j).net.count ≤ w*(2*w+7)+1 := by
  apply le_trans (any_count _ (c := 2*w+3) ?_)
  · simp [Nat.add_assoc]
  · intro a ha
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp ha
    rw [count_band]
    have h₁ := distance_count s
    have h₂ := shiftedBit_count left s j
    omega

/-- A fixed bounded-fan-in network on the little-endian input pair. -/
def network (op : Op) (w : ℕ) : BooleanNetwork (w+w) w :=
  vector fun j => match op with
    | .bitAnd => (lhs j).band (rhs j)
    | .bitOr => (lhs j).bor (rhs j)
    | .bitXor => (lhs j).bxor (rhs j)
    | .shiftLeft => shift true j
    | .shiftRight => shift false j

/-- Evaluation recovers the corresponding bit in the RAM word. -/
theorem network_correct {w : ℕ} (op : Op) (x y : Word w) (j : Fin w) :
    (network op w).eval
        (Fin.append (fun i : Fin w => x.val.testBit i.val) (fun i : Fin w => y.val.testBit i.val)) j =
      (op.toBinary.eval x y).val.testBit j.val := by
  change (network op w).eval (pins x y) j = _
  rw [network, eval_vector]
  cases op
  case bitAnd => simp [Op.toBinary, BinaryOp.eval, Fin.ofNat, j.isLt]
  case bitOr => simp [Op.toBinary, BinaryOp.eval, Fin.ofNat, j.isLt]
  case bitXor => simp [Op.toBinary, BinaryOp.eval, Fin.ofNat, j.isLt]
  case shiftLeft =>
    apply Bool.eq_iff_iff.mpr
    rw [shift_true]
    by_cases h : y.val < w <;> simp [Op.toBinary, BinaryOp.eval, Fin.ofNat, h, j.isLt]
  case shiftRight =>
    apply Bool.eq_iff_iff.mpr
    rw [shift_true]
    by_cases h : y.val < w <;> simp [Op.toBinary, BinaryOp.eval, Fin.ofNat, h, j.isLt]

/-- The decoder uses at most cubic size, including both zero-width and
out-of-range shift cases. -/
theorem network_count (op : Op) (w : ℕ) :
    (network op w).net.count ≤ 16*(w+1)^3 := by
  apply le_trans (count_vector_le _ (c := w*(2*w+7)+8) ?_)
  · ring_nf
    omega
  · intro j
    cases op <;> simp only
    · simp [lhs, rhs]
    · simp [lhs, rhs]
    · simp [lhs, rhs]
    · have := shift_count true j; omega
    · have := shift_count false j; omega

end ThreeFlat.Diagonal.TraceBitwiseOps

end OAI
