import OAI.Hierarchy.DescentWalshInteger
import OAI.Hierarchy.DescentIntegerRow
import OAI.Hierarchy.DescentGLNativeSelection

namespace OAI
/-! # Integer Walsh scores at all candidate row indices -/

namespace Hierarchy.DescentWalshTables
open scoped BigOperators
open DescentIntegerScale

/-- The zero-frequency output is the sum of the inputs. Adding it to
every frequency yields twice every integral kernel sum. -/
def scoreRows {k : ℕ} (input : Table ℤ k) : Table ℤ k × ℕ :=
  let spectrum := input.transform
  let total := spectrum.1.read 0
  let scores := Table.combine (·+·) (Table.tabulate k fun _ => total) spectrum.1
  (scores.1, spectrum.2 + scores.2)

theorem scoreRows_cost {k : ℕ} (input : Table ℤ k) :
    (scoreRows input).2 = (k+1)*2^k := by
  simp only [scoreRows, Table.transform_cost, Table.combine_cost]
  ring

theorem scoreRows_read {k : ℕ} (input : Table ℤ k) (f : Bits k) :
    (scoreRows input).1.read f =
      2 * ∑ d ∈ Finset.univ.filter (fun d => binaryRow f d=0), input.read d := by
  classical
  let x (d : Bits k) : ℝ := input.read d
  have zero : coefficient x 0 = ∑ d,x d := by
    simp [coefficient,character_row,sign,binaryRow_apply]
  have est := DescentRowScore.kernel_score (binaryRow f) x
  have casted : ((scoreRows input).1.read f : ℝ) =
      2 * ∑ d ∈ Finset.univ.filter (fun d => binaryRow f d=0), x d := by
    simp only [scoreRows,Table.combine_read,Table.tabulate_read,Int.cast_add,integerTransform_cast]
    change coefficient x 0 + coefficient x f = _
    rw [zero,coefficient_eq_walsh]
    linarith
  dsimp only [x] at casted
  exact_mod_cast casted

noncomputable section
open DescentGL

/-- Binary coefficient-vector indexing agrees with the indices used for ties
by the actual row-selection controller. -/
theorem binaryRow_index {k : ℕ} (f : Bits k) :
    rowIndex k (binaryRow f) = finFunctionFinEquiv f := by
  classical
  change finFunctionFinEquiv ((Pi.basisFun (ZMod 2) (Fin k)).dualBasis.equivFun (binaryRow f))
    = finFunctionFinEquiv f
  apply congrArg (fun z : Bits k => finFunctionFinEquiv z)
  funext i
  simp [Module.Basis.equivFun_apply,Pi.basisFun_apply,binaryRow_apply,Pi.single_apply]

variable {h r : ℕ}
local notation "k" => (h+1)+r

/-- Each integral input at a difference is aggregated only once per prefix.
The candidate functional itself plays no role in preparing this input. -/
def rowInput (base : Layout k) (W : Fin (r+1) → Bits k → ℕ) : Table ℤ k :=
  Table.tabulate k fun d =>
    if d≠0 ∧ headRows (show h≤k by omega) (base d)=0
    then (differenceNumerator r W d : ℤ) else 0

/-- The read at a given binary index is twice the exact integral numerator
of that candidate's conditional collision score. This includes the last row. -/
theorem scoreRows_indexed (base : Layout k) (W : Fin (r+1) → Bits k → ℕ)
    (i : Fin (2^k)) :
    (scoreRows (rowInput base W)).1.read (finFunctionFinEquiv.symm i) =
      2 * (rowNumerator r W (surviving base ((rowIndex k).symm i)) : ℤ) := by
  classical
  let f : Bits k := finFunctionFinEquiv.symm i
  change (scoreRows (rowInput base W)).1.read f = _
  have idx : rowIndex k (binaryRow f) = i :=
    (binaryRow_index f).trans (finFunctionFinEquiv.apply_symm_apply i)
  have row : binaryRow f = (rowIndex k).symm i :=
    (rowIndex k).injective (idx.trans ((rowIndex k).apply_symm_apply _).symm)
  rw [scoreRows_read (rowInput base W) f,row]
  congr 1
  simp only [rowInput,Table.tabulate_read,rowNumerator,Nat.cast_sum,surviving,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d=0 <;>
    by_cases old : headRows (show h≤k by omega) (base d)=0 <;>
    by_cases hits : (rowIndex k).symm i d=0 <;> simp [hd,old,hits]

theorem scoreRows_compare (base : Layout k) (W : Fin (r+1) → Bits k → ℕ)
    (i j : Fin (2^k)) {q : ℕ} (hq : 0<q) (hr : 0<r) :
    (scoreRows (rowInput base W)).1.read (finFunctionFinEquiv.symm i) ≤
        (scoreRows (rowInput base W)).1.read (finFunctionFinEquiv.symm j) ↔
      conditionalRowScore base (fun l d => (W l d.val : ℝ)/(q:ℝ)^2) ((rowIndex k).symm i) ≤
        conditionalRowScore base (fun l d => (W l d.val : ℝ)/(q:ℝ)^2) ((rowIndex k).symm j) := by
  rw [scoreRows_indexed,scoreRows_indexed,compare_conditionalRows _ _ _ hq hr]
  omega

end
end Hierarchy.DescentWalshTables

end OAI
