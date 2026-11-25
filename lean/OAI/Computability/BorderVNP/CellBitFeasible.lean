import OAI.Computability.BorderVNP.CellAddressEvaluator
import OAI.Computability.RationalHitting.UnaryArithmetic
import Mathlib.Data.Nat.Bitwise

/-! # Reading an indexed bit from a binary word in polynomial time

The index itself is binary. The bounded scan runs at most once per digit of the word,
including when the numerical index lies far beyond the end.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open RationalHitting RationalHitting.StackLanguage Function

private def tailProcedure : Procedure BitWord.val BitWord.val (fun w => ⟨w.val.tail⟩) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .drop ()
  bound := TimeBound.variable
  correct w := by
    refine ⟨1, by simp, ?_⟩
    simpa [single] using Eval.drop () (single () w.val)
  size w := by simp; omega

private def headProcedure : Procedure BitWord.val boolCode (fun w => w.val.headD false) where
  Registers := Unit
  finite := inferInstance
  decEq := inferInstance
  input := ()
  output := ()
  program := .branch () (.push () false) (.seq (clear ()) (.push () false))
    (.seq (clear ()) (.push () true))
  bound := 2*TimeBound.variable + 4
  correct w := by
    rcases w with ⟨_ | ⟨b,l⟩⟩
    · refine ⟨2, by simp, ?_⟩
      have h : Eval (.push () false) (single () []) (single () [false]) 1 := by
        simpa [single] using Eval.push () false (single () [])
      exact Eval.branchNone (by simp) h
    · have h := Eval.seq (eval_clear_single () (b::l)) (Eval.push () b (fun _ : Unit => []))
      have e : Eval (.seq (clear ()) (.push () b)) (single () (b::l)) (single () [b])
          (2*(b::l).length + 3) := by convert h using 1 <;> simp [single]; omega
      refine ⟨1 + (2*(b::l).length + 3), by simp; omega, ?_⟩
      cases b
      · exact Eval.branchFalse (ls := l) (by simp) e
      · exact Eval.branchTrue (ls := l) (by simp) e
  size w := by simp

private abbrev BitState := BitWord × ℕ

private def step (s : BitState) : BitState :=
  if s.2 = 0 then s else (⟨s.1.val.tail⟩,s.2-1)

open Address
open private nat_sub from OAI.Computability.BorderVNP.CellAddressEvaluator

private theorem step_poly : Poly step := by
  have hp : Poly (fun s : BitState => s.2-1) := nat_sub.comp (show Poly (fun s : BitState => (s.2,1)) by fun_prop)
  have ht : Poly (fun s : BitState => BitWord.mk s.1.val.tail) :=
    (show Poly (fun w : BitWord => BitWord.mk w.val.tail) from ⟨tailProcedure⟩).comp Poly.fst
  exact (Poly.cond (Poly.natZero.comp Poly.snd) Poly.id (ht.pair hp)).of_eq (by simp [step])

private theorem step_size (s : BitState) : (Coding.code (step s)).length ≤ (Coding.code s).length := by
  by_cases h : s.2 = 0
  · simp [step, h]
  · change (pairCode BitWord.val Nat.bits (step s)).length ≤ (pairCode BitWord.val Nat.bits s).length
    simp only [step, h, ↓reduceIte]
    simp only [pairCode_length, Nat.size_eq_bits_len, List.length_tail]
    have := Nat.size_le_size (Nat.sub_le s.2 1)
    omega

private theorem iterate_size (s : BitState) (k : ℕ) :
    (Coding.code (step^[k] s)).length ≤ (Coding.code s).length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [iterate_succ_apply']; exact (step_size _).trans ih

private theorem scan_correct (l : List Bool) (i : ℕ) :
    ((step^[l.length] (⟨l⟩,i)).1.val.headD false) = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero =>
      have fixed : step (⟨b::l⟩,0) = (⟨b::l⟩,0) := rfl
      rw [iterate_fixed fixed]; rfl
    | succ i =>
      rw [List.length_cons, iterate_succ_apply]
      exact ih i

/-- A concrete binary stack procedure for arbitrary bit positions. Its clock is polynomial
in the binary input length even when the requested bit is beyond the word. -/
theorem testBit_poly : Poly (fun a : ℕ × ℕ => a.1.testBit a.2) := by
  have hi := step_poly.iterate TimeBound.variable (by
    intro n s i _
    have h := iterate_size s i
    simp only [TimeBound.eval_variable, pairCode_length]
    omega)
  have hw : Poly (fun n : ℕ => BitWord.mk n.bits) :=
    (Feasible.id Nat.bits).recode _ _ _ id (by intro n; rfl) (by intro n; rfl)
  have hs : Poly (fun a : ℕ × ℕ => (Unary.mk a.1.bits.length, (BitWord.mk a.1.bits,a.2))) :=
    (Poly.natBitLength.comp Poly.fst).pair ((hw.comp Poly.fst).pair Poly.snd)
  have hh : Poly (fun w : BitWord => w.val.headD false) := ⟨headProcedure⟩
  apply (hh.comp (Poly.fst.comp (hi.comp hs))).of_eq
  intro a
  rw [scan_correct, Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
  rfl

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
