import OAI.Computability.BorderVNP.CellAddressLength
import OAI.Computability.BorderVNP.CellGeneratorWire

/-! # Length of the sparse program actually consumed by the private machine

The serialized record stream keeps one copy of each loop body, and one copy of each
branch. Framing multiplies length only when a program crosses a control level.
Sequences are simply concatenated, independent of their nesting.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open CellSparse RationalHitting.StackLanguage

/-- Concatenating two command directories concatenates their framed streams. -/
theorem records_append (s t : List (List Bool)) : records (s++t) = records s ++ records t := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [records, ih]

private theorem single_length (w : List Bool) : (records [w]).length = 2*w.length+2 := by
  simp [records, codeWord_length, Nat.add_assoc]

private theorem bounded_expr (d M J : ℕ) (e : NatExpr) (hm : e.field ≤ M) (hj : e.lexical ≤ J) :
    (exprBits d e).length ≤ 64^(d+1)*(1+M.size+J) :=
  (Address.pack_length d e).trans (Nat.mul_le_mul_left _ (by have := Nat.size_le_size hm; omega))

private theorem bounded_stream (d M J : ℕ) (s : Stmt) (h : ℕ)
    (fit : s.FitsDepth d h) (hf : s.field ≤ M) (hj : s.lexical ≤ J) :
    (serialized d s).length ≤ (16^(h+1)*(64^(d+1)*(1+M.size+J)))*s.mass := by
  let B := 64^(d+1)*(1+M.size+J)
  have hB : 2 ≤ B := by
    have hpow : 64^1 ≤ 64^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have := Nat.mul_le_mul (show 2 ≤ 64^(d+1) by norm_num at hpow; omega) (show 1 ≤ 1+M.size+J by omega)
    simpa [B] using this
  have hframe (k : ℕ) : 16*B ≤ 16^(k+1)*B := by
    have hh : 16^1 ≤ 16^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.mul_le_mul_right B (by simpa using hh)
  have addr (e : NatExpr) (hm : e.field ≤ M) (he : e.lexical ≤ J) : (exprBits d e).length ≤ B :=
    bounded_expr d M J e hm he
  change (serialized d s).length ≤ (16^(h+1)*B)*s.mass
  induction s generalizing h with
  | nil => simp [serialized,wire,records,Stmt.mass]
  | fixed op =>
    cases op <;> simp only [serialized, wire, Stmt.mass, single_length, List.length_append,
      List.length_cons, List.length_nil, Op.bits, Nat.mul_one] at *
    case read k =>
      have := addr (.lit k) hf (Nat.zero_le _)
      have := hframe h
      omega
    all_goals have := hframe h; omega
  | read e =>
    have := addr e hf hj
    have := hframe h
    simp only [serialized, wire, single_length, List.length_append, List.length_cons,
      List.length_nil, Stmt.mass, Nat.mul_add, Nat.mul_one]
    omega
  | bit a b =>
    have ha := addr a (max_le_iff.mp hf).1 (max_le_iff.mp hj).1
    have hb := addr b (max_le_iff.mp hf).2 (max_le_iff.mp hj).2
    have := hframe h
    simp only [serialized, wire, single_length, List.length_append, List.length_cons,
      List.length_nil, Stmt.mass, Nat.mul_add, Nat.mul_one, prod_code_length]
    unfold exprBits at ha hb
    omega
  | seq a b ia ib =>
    have ha := ia h fit.1 (max_le_iff.mp hf).1 (max_le_iff.mp hj).1
    have hb := ib h fit.2 (max_le_iff.mp hf).2 (max_le_iff.mp hj).2
    simp only [serialized, wire, records_append, List.length_append, Stmt.mass, Nat.mul_add, Nat.mul_one] at *
    omega
  | loop e s ih =>
    cases h with
    | zero => exact (Nat.lt_irrefl 0 fit.1).elim
    | succ h =>
      have ha := addr e (max_le_iff.mp hf).1 (max_le_iff.mp hj).1
      have hs := ih h fit.2.2 (max_le_iff.mp hf).2 (max_le_iff.mp hj).2
      have := hframe h
      simp only [serialized, wire, single_length, List.length_append, List.length_cons,
        List.length_nil, Loop.payload, codeWord_length, Stmt.mass, Nat.mul_add, Nat.mul_one] at *
      rw [pow_succ (16 : ℕ) (h+1), Nat.mul_right_comm (16^(h+1)) 16 B,
        Nat.mul_comm (16^(h+1)*B) 16]
      simp only [Nat.mul_assoc] at hs ⊢
      omega
  | ifEq a b s t ihs iht =>
    cases h with
    | zero => exact (Nat.lt_irrefl 0 fit.1).elim
    | succ h =>
      have hab := addr (difference a b) (by rw [difference_field]; exact (max_le_iff.mp hf).1)
        (by rw [difference_lexical]; exact (max_le_iff.mp hj).1)
      have hs := ihs h fit.2.2.1 (max_le_iff.mp (max_le_iff.mp hf).2).1
        (max_le_iff.mp (max_le_iff.mp hj).2).1
      have ht := iht h fit.2.2.2 (max_le_iff.mp (max_le_iff.mp hf).2).2
        (max_le_iff.mp (max_le_iff.mp hj).2).2
      have := hframe h
      simp only [serialized, wire, single_length, List.length_append, List.length_cons,
        List.length_nil, branchPayload, codeWord_length, Stmt.mass, Nat.mul_add, Nat.mul_one] at *
      rw [pow_succ (16 : ℕ) (h+1), Nat.mul_right_comm (16^(h+1)) 16 B,
        Nat.mul_comm (16^(h+1)*B) 16]
      simp only [Nat.mul_assoc] at hs ht ⊢
      omega

/-- Binary size of the entire compact record stream used by the actual finite dispatcher. -/
theorem serialized_length (d h : ℕ) (s : Stmt) (fit : s.FitsDepth d h) :
    (serialized d s).length ≤ (16^(h+1)*64^(d+1))*s.mass*(1+s.field.size+s.lexical) := by
  have H := bounded_stream d s.field s.lexical s h fit le_rfl le_rfl
  convert H using 1
  ring

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
