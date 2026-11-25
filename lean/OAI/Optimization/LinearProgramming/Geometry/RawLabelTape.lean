import OAI.Optimization.LinearProgramming.Geometry.LabelBuffers
import Mathlib.Data.List.OfFn

/-! A scalar-only tape consisting of D in row-major order, then E, then one price per entry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Matrix
variable {K : Type} {r s n : ℕ}

def matrixWords (D : Matrix (Fin r) (Fin n) K) : List K := List.ofFn fun j : Fin (r*n) =>
  D (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

@[simp] theorem matrixWords_length (D : Matrix (Fin r) (Fin n) K) : (matrixWords D).length=r*n := by simp [matrixWords]

theorem matrixWord_lt (a : Fin r) (b : Fin n) : a.val*n+b.val<r*n := calc
  _ < a.val*n+n := Nat.add_lt_add_left b.isLt _
  _ = (a.val+1)*n := by ring
  _ ≤ r*n := Nat.mul_le_mul_right n a.isLt

theorem matrixWords_get (D : Matrix (Fin r) (Fin n) K) (a : Fin r) (b : Fin n) :
    (matrixWords D)[a.val*n+b.val]?=some (D a b) := by
  have hlt := matrixWord_lt a b
  have eq : (⟨a.val*n+b.val,hlt⟩ : Fin (r*n))=finProdFinEquiv (a,b) := by
    apply Fin.ext; change a.val*n+b.val=b.val+n*a.val; ac_rfl
  unfold matrixWords
  rw [List.getElem?_ofFn, dite_eq_left hlt,eq]
  simp only [Equiv.symm_apply_apply]

def rawTape (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K) : List K :=
  matrixWords D ++ (matrixWords E ++ List.ofFn t)

@[simp] theorem rawTape_length (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K) :
    (rawTape D E t).length = r*n+s*n+n := by simp [rawTape,Nat.add_assoc]

theorem rawTape_primal (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K)
    (a : Fin r) (b : Fin n) : (rawTape D E t)[a.val*n+b.val]?=some (D a b) := by
  rw [rawTape,List.getElem?_append_left (by simpa using matrixWord_lt a b),matrixWords_get]

theorem rawTape_dual (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K)
    (a : Fin s) (b : Fin n) : (rawTape D E t)[r*n+(a.val*n+b.val)]?=some (E a b) := by
  rw [rawTape,List.getElem?_append_right (by simp),matrixWords_length,Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa using matrixWord_lt a b),matrixWords_get]

theorem rawTape_price (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K)
    (b : Fin n) : (rawTape D E t)[r*n+(s*n+b.val)]?=some (t b) := by
  rw [rawTape,List.getElem?_append_right (by simp),matrixWords_length,Nat.add_sub_cancel_left,
    List.getElem?_append_right (by simp),matrixWords_length,Nat.add_sub_cancel_left]
  simp

theorem rawTape_safe [Zero K] (P : K → Prop) (p0 : P 0) (D : Matrix (Fin r) (Fin n) K)
    (E : Matrix (Fin s) (Fin n) K) (t : Fin n → K) (pd : ∀ a b, P (D a b)) (pe : ∀ a b, P (E a b))
    (pt : ∀ b, P (t b)) (j : ℕ) : P (((rawTape D E t)[j]?).getD 0) := by
  cases h : (rawTape D E t)[j]? with
  | none => exact p0
  | some a =>
    have mem := List.mem_of_getElem? h
    simp [rawTape,matrixWords,List.mem_ofFn] at mem
    rcases mem with ⟨v,rfl⟩ | ⟨v,rfl⟩ | ⟨v,rfl⟩
    · exact pd _ _
    · exact pe _ _
    · exact pt _

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
