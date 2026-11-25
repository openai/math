import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Find

/-! # Compiling binary column changes to XOR passes

A single program handles every number of columns and every choice of a bit inside a
slot. One instruction adds its source axis into its destination simultaneously in
all columns. The synthesis search depends only on the finite matrix. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelColumn

abbrev Word (A : ℕ) := List (Fin A × Fin A)
abbrev BinaryMatrix (A : ℕ) := Matrix (Fin A) (Fin A) (ZMod 2)
abbrev Address (A f K : ℕ) := Fin A → Fin f → Fin K → ZMod 2

variable {A f K : ℕ}

/-- A repeated axis encodes a no-op, so every decoded word is reversible. -/
def gateMatrix (g : Fin A × Fin A) : BinaryMatrix A :=
  if g.1 = g.2 then 1 else Matrix.transvection g.1 g.2 1

def wordMatrix (w : Word A) : BinaryMatrix A := (w.map gateMatrix).prod

theorem exists_word (M : BinaryMatrix A) (hM : M.det ≠ 0) :
    ∃ w : Word A, wordMatrix w = M := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (n := Fin A) (𝕜 := ZMod 2)
    (fun N => ∃ w : Word A, wordMatrix w = N) M hM ?_ ?_ ?_
  · intro d hd
    refine ⟨[], ?_⟩
    rw [Matrix.det_diagonal] at hd
    have h₁ (i : Fin A) : d i = 1 := by
      have h₀ : d i ≠ 0 :=
        Finset.prod_ne_zero_iff.mp hd i (Finset.mem_univ i)
      have hbit : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact (hbit _).resolve_left h₀
    simp [wordMatrix, funext h₁]
  · rintro ⟨i,j,hij,c⟩
    have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hc c with rfl | rfl
    · exact ⟨[], by simp [wordMatrix]⟩
    · exact ⟨[(i,j)], by simp [wordMatrix, gateMatrix, hij]⟩
  · rintro B C _ _ ⟨w,rfl⟩ ⟨v,rfl⟩
    exact ⟨w ++ v, by simp [wordMatrix]⟩

private def decodeWord (A n : ℕ) : Word A :=
  (Encodable.decode (α := Word A) n).getD []

private theorem search_terminates (M : BinaryMatrix A) (hM : M.det ≠ 0) :
    ∃ n, wordMatrix (decodeWord A n) = M := by
  obtain ⟨w, hw⟩ := exists_word M hM
  exact ⟨Encodable.encode w, by simpa [decodeWord] using hw⟩

/-- A terminating enumeration of finite XOR programs for the fixed matrix. -/
def compile (M : BinaryMatrix A) (hM : M.det ≠ 0) : Word A :=
  decodeWord A (Nat.find (search_terminates M hM))

theorem wordMatrix_compile (M : BinaryMatrix A) (hM : M.det ≠ 0) :
    wordMatrix (compile M hM) = M :=
  Nat.find_spec (search_terminates M hM)

def pass (g : Fin A × Fin A) (offset : Fin K) (x : Address A f K) : Address A f K :=
  fun a c t => if g.1 ≠ g.2 ∧ a = g.1 ∧ t = offset then x a c t + x g.2 c t else x a c t

/-- Matrices multiply from the left, so the last letter acts first. -/
def execute (w : Word A) (offset : Fin K) (x : Address A f K) : Address A f K :=
  w.foldr (fun g => pass g offset) x

theorem pass_at (g : Fin A × Fin A) (offset : Fin K) (x : Address A f K) (c : Fin f) :
    (fun a => pass g offset x a c offset) =
      (gateMatrix g).mulVec (fun a => x a c offset) := by
  by_cases h : g.1 = g.2
  · simp [gateMatrix, pass, h]
  · funext a
    simp only [gateMatrix, h, ↓reduceIte, Matrix.transvection, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec, one_mul, Pi.add_apply]
    by_cases ha : a = g.1
    · simp [pass, h, ha]
    · simp [pass, h, ha]

/-- This is equation (reindex) at the selected offset, with every other bit untouched. -/
theorem execute_eq (w : Word A) (offset : Fin K) (x : Address A f K) (c : Fin f) (t : Fin K) :
    (fun a => execute w offset x a c t) =
      if t = offset then (wordMatrix w).mulVec (fun a => x a c t) else fun a => x a c t := by
  induction w with
  | nil => simp [execute, wordMatrix]
  | cons g w ih =>
    change (fun a => pass g offset (execute w offset x) a c t) = _
    split_ifs with ht
    · subst t
      rw [pass_at]
      simp at ih
      rw [ih, Matrix.mulVec_mulVec]
      rfl
    · simpa [pass, ht] using ih

theorem execute_compile (M : BinaryMatrix A) (hM : M.det ≠ 0) (offset : Fin K)
    (x : Address A f K) (c : Fin f) (t : Fin K) :
    (fun a => execute (compile M hM) offset x a c t) =
      if t = offset then M.mulVec (fun a => x a c t) else fun a => x a c t := by
  rw [execute_eq, wordMatrix_compile]

end KernelColumn

end NearSquareRoot
end Computability
end OAI
