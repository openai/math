import OAI.Optimization.LinearProgramming.Compression.MinorLoadData
import OAI.Optimization.LinearProgramming.Compression.MinorOrder
import Mathlib.Logic.Equiv.Fin.Basic

/-! The loader view for a request selecting either of two contiguous input matrices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

variable {K : Type*}

/-- Address-bank representation of the header and two finite index arrays. -/
def indexData (v : Layout K) (a : ℕ) : ℕ :=
  if a < 6 then [v.src,v.n,v.k,v.rowArray,v.colArray,v.dst][a]?.getD 0
  else if hr : v.rowArray ≤ a ∧ a < v.rowArray + v.k then
    (v.row ⟨a-v.rowArray, by omega⟩).val
  else if hc : v.colArray ≤ a ∧ a < v.colArray + v.k then
    (v.col ⟨a-v.colArray, by omega⟩).val
  else 0

theorem indexData_row (v : Layout K) (i : Fin v.k) : indexData v (v.rowArray+i.val) = (v.row i).val := by
  have hi := i.isLt
  have ha := v.rowArray_ge
  simp [indexData, show ¬v.rowArray+i.val < 6 by omega, show v.rowArray+i.val < v.rowArray+v.k by omega]

theorem indexData_col (v : Layout K) (hgap : v.rowArray+v.k ≤ v.colArray) (i : Fin v.k) :
    indexData v (v.colArray+i.val) = (v.col i).val := by
  have hi := i.isLt
  have ha := v.colArray_ge
  simp [indexData, show ¬v.colArray+i.val < 6 by omega, show ¬v.colArray+i.val < v.rowArray+v.k by omega,
    show v.colArray+i.val < v.colArray+v.k by omega]

/-- A row-major matrix entry, with zero outside the input. -/
def matrixCell [Zero K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (a : ℕ) : K :=
  if h : a < m*n then
    let ij := finProdFinEquiv.symm (⟨a,h⟩ : Fin (m*n))
    A ij.1 ij.2
  else 0

theorem matrixCell_at [Zero K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
    matrixCell A (i.val*n+j.val) = A i j := by
  have h := flat_lt i.isLt j.isLt
  rw [matrixCell, dite_eq_left h]
  have hi : (⟨i.val*n+j.val,h⟩ : Fin (m*n)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val = j.val+n*i.val
    ac_rfl
  simp [hi]

/-- Scalars 0–6 are reserved for the determinant kernel. The rows of D occupy the following
`rD*n` registers and the rows
of E immediately follow them. Unoccupied registers initially contain zero. -/
def stackedData [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (a : ℕ) : K :=
  if a < 7 then 0 else if a-7 < rD*n then matrixCell D (a-7) else matrixCell E (a-7-rD*n)

theorem stackedData_left [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (i : Fin rD) (j : Fin n) :
    stackedData D E (7+i.val*n+j.val) = D i j := by
  have h := flat_lt i.isLt j.isLt
  rw [stackedData, ite_eq_right (show ¬7+i.val*n+j.val < 7 by omega),
    show 7+i.val*n+j.val-7=i.val*n+j.val by omega, ite_eq_left h, matrixCell_at]

theorem stackedData_right [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (i : Fin rE) (j : Fin n) :
    stackedData D E (7+rD*n+i.val*n+j.val) = E i j := by
  have hr : ¬7+rD*n+i.val*n+j.val-7 < rD*n := by omega
  have hi : 7+rD*n+i.val*n+j.val-7-rD*n=i.val*n+j.val := by omega
  rw [stackedData, ite_eq_right (show ¬7+rD*n+i.val*n+j.val < 7 by omega),
    ite_eq_right hr, hi, matrixCell_at]

def pairLayout {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K) :
    PairMinorIndex rD rE n → Layout K
  | .inl ⟨k,row,col⟩ => {
      m := rD, n := n, k := k.val, src := 7, dst := 7 + (rD+rE)*n,
      rowArray := 16, colArray := 16+k.val, matrix := D, row := row, col := col,
      src_pos := by decide, disjoint := Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right ..)) 7,
      rowArray_ge := le_rfl, colArray_ge := Nat.le_add_right .. }
  | .inr ⟨k,row,col⟩ => {
      m := rE, n := n, k := k.val, src := 7+rD*n, dst := 7 + (rD+rE)*n,
      rowArray := 16, colArray := 16+k.val, matrix := E, row := row, col := col,
      src_pos := by omega, disjoint := by rw [Nat.add_mul, Nat.add_assoc],
      rowArray_ge := le_rfl, colArray_ge := Nat.le_add_right .. }

/-- Construct the two register banks of the fixed loader for the actual request. -/
def pairMemory [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K) (E : Matrix (Fin rE) (Fin n) K)
    (u : PairMinorIndex rD rE n) : Memory K := ⟨stackedData D E, indexData (pairLayout D E u)⟩

theorem pairMemory_input [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (u : PairMinorIndex rD rE n) :
    Input (pairLayout D E u) (pairMemory D E u) := by
  have gap : (pairLayout D E u).rowArray + (pairLayout D E u).k ≤ (pairLayout D E u).colArray := by
    cases u <;> rfl
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,indexData_row _,indexData_col _ gap,?_⟩
  cases u with
  | inl val => exact stackedData_left D E
  | inr val => exact stackedData_right D E

theorem pairMemory_safe [Zero K] {rD rE n : ℕ} (D : Matrix (Fin rD) (Fin n) K)
    (E : Matrix (Fin rE) (Fin n) K) (u : PairMinorIndex rD rE n) {P : K → Prop}
    (hz : P 0) (hD : ∀ i j, P (D i j)) (hE : ∀ i j, P (E i j)) :
    ∀ a, P ((pairMemory D E u).data a) := by
  have cell {m : ℕ} (M : Matrix (Fin m) (Fin n) K) (h : ∀ i j, P (M i j)) (a : ℕ) :
      P (matrixCell M a) := by
    unfold matrixCell
    split
    · exact h _ _
    · exact hz
  intro a
  change P (stackedData D E a)
  unfold stackedData
  split
  · exact hz
  · split
    · exact cell D hD _
    · exact cell E hE _

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
