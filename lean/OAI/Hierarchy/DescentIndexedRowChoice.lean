import OAI.Hierarchy.DescentGLSpanBitmap
import OAI.Hierarchy.DescentIntegerRowScan
import OAI.Hierarchy.DescentWalshRowTable

namespace OAI
/-! # Computing the specified row from its integer Walsh scores and span bitmap -/

namespace Hierarchy.DescentGL

open DescentIntegerScale DescentWalshTables

/-- Drop the least significant bit of a bounded binary address. -/
private def nextAddress {k : ℕ} (i : Fin (2^(k+1))) : Fin (2^k) :=
  ⟨i.val/2,(Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [pow_succ] using i.isLt)⟩

/-- Traverse the binary table directly from its integer index. Each branch
uses one low-bit extraction, one right shift, and one branch selection. -/
def readIndex : {k : ℕ} → Table ℤ k → Fin (2^k) → ℤ × ℕ
  | 0,.scalar x,_ => (x,1)
  | _+1,.branch a b,i =>
    let child := if i.val%2=0 then a else b
    let answer := readIndex child (nextAddress i)
    (answer.1,answer.2+3)

theorem readIndex_cost {k : ℕ} (table : Table ℤ k) (i : Fin (2^k)) :
    (readIndex table i).2=3*k+1 := by
  induction table with
  | scalar x => rfl
  | @branch k a b ha hb => by_cases e : i.val%2=0 <;> simp [readIndex,e,ha,hb,Nat.mul_succ]

set_option backward.isDefEq.respectTransparency false in
theorem readIndex_eq {k : ℕ} (table : Table ℤ k) (i : Fin (2^k)) :
    (readIndex table i).1=table.read (finFunctionFinEquiv.symm i) := by
  induction table with
  | scalar x => rfl
  | @branch k a b ha hb =>
    have head : (finFunctionFinEquiv.symm i : DescentGL.Bits (k+1)) 0=0 ↔ i.val%2=0 := by
      change (⟨i.val/2^(0:ℕ)%2, _⟩ : Fin 2)=0 ↔ _
      simp [Fin.ext_iff]
    have tail : Fin.tail (finFunctionFinEquiv.symm i : DescentGL.Bits (k+1)) =
        finFunctionFinEquiv.symm (nextAddress i) := by
      funext j
      apply Fin.ext
      change i.val / 2^(j.val+1) % 2 = (i.val/2) / 2^j.val % 2
      rw [pow_succ' (2:ℕ) j.val,Nat.div_div_eq_div_mul]
    change _ = if (finFunctionFinEquiv.symm i : DescentGL.Bits (k+1)) 0=0
      then a.read (Fin.tail (finFunctionFinEquiv.symm i))
      else b.read (Fin.tail (finFunctionFinEquiv.symm i))
    by_cases e : i.val%2=0
    · simp only [readIndex,ite_eq_left e,ite_eq_left (head.mpr e)]
      exact (ha _).trans (congrArg a.read tail.symm)
    · simp only [readIndex,ite_eq_right e,ite_eq_right (fun z => e (head.mp z))]
      exact (hb _).trans (congrArg b.read tail.symm)

/-- Construct the exclusion bitmap, compute the spectrum once, then read a
score only when its row is eligible. The counter includes the read traversal. -/
def indexedRowChoice {h k : ℕ} (rows : Fin h → DescentGL.Bits k) (input : Table ℤ k) :
    Option (Fin (2^k)) × ℕ :=
  let excluded := spanBitmap rows
  let table := scoreRows input
  let result := leastRowMeasured excluded.1 (readIndex table.1)
  (result.1,excluded.2+table.2+result.2)

/-- All phases together use polynomially many operations per possible row. -/
theorem indexedRowChoice_cost_le {h k : ℕ} (hk : h≤k) (rows : Fin h → DescentGL.Bits k)
    (input : Table ℤ k) : (indexedRowChoice rows input).2 ≤ (k*(2*k+2)+4*k+8)*2^k := by
  let bitmap := (spanBitmap rows).1
  let indexed := readIndex (scoreRows input).1
  have scan := leastRowMeasured_bound bitmap indexed (cap:=3*k+1) (fun i => (readIndex_cost _ i).le)
  simp only [indexedRowChoice,spanBitmap_cost,scoreRows_cost]
  calc
    _ ≤ (3*2^k+2^k+2^k*(k*(2*k+2)+1))+(k+1)*2^k + 2^k*(3*k+1+1) := by
      have hp : (2:ℕ)^h≤2^k := Nat.pow_le_pow_right (by decide) hk
      have v := coefficientListVisits_add_two h
      have visits : coefficientListVisits h≤3*2^k := by omega
      gcongr
    _ = _ := by ring

noncomputable section
variable {h r : ℕ}
local notation "k" => (h+1)+r

/-- The computed word is the native least-index minimizer in the actual
GL prefix menu, including the last row where all legal scores vanish. -/
theorem indexedRowChoice_exact (base : Layout k) (W : Fin (r+1) → DescentGL.Bits k → ℕ)
    {q : ℕ} (hq : 0<q) :
    (indexedRowChoice (storedRows (show h<k by omega) base) (rowInput base W)).1 =
      some (chosenIndex (show h<k by omega) base
        (conditionalRowScore base (fun l d => (W l d.val : ℝ)/(q:ℝ)^2))) := by
  change (leastRowMeasured _ _).1=_
  rw [leastRowMeasured_same]
  simp only [readIndex_eq]
  apply leastRow_eq_chosenIndex
  · exact spanBitmap_legal _ base
  · intro i j
    by_cases hr : 0<r
    · exact scoreRows_compare base W i j hq hr
    · obtain rfl : r=0 := by omega
      simp [scoreRows_indexed,conditionalRowScore_eq_integer,rowNumerator_zero]

end
end Hierarchy.DescentGL

end OAI
