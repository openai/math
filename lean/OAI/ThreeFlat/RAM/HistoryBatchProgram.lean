import OAI.ThreeFlat.Diagonal.HistoryBatchRows
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # A native nine-column postorder task generator for motif batches -/

namespace ThreeFlat.RAM.HistoryBatchProgram

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr Diagonal.HistoryContraction.Tree
open scoped Fin.CommRing

private abbrev E := Formula 14
private abbrev v (i : Fin 14) : E := .reg i

private def pre (a b : E) : E := add (mul (lt (v 0) (v 1) (v 0) (v 1)) a) (mul (sub (v 0) (v 1)) b)

/-- `[child,leftCount,rightCount, left/right arity, left/right rows,
left/right bits, stream,map,node,task,column]`. The first five columns
are the complete operand record read by HistoryCommandTable. -/
def args (i r s : ℕ) (A B : BatchRows.Size) (base : Addresses) (col : Fin 9) : Fin 14 → ℕ :=
  ![i,r,s,A.arity,B.arity,A.rows,B.rows,A.bits,B.bits,base.stream,base.maps,base.nodes,base.tasks,col.val]

def recordWord (q : Copy) : Fin 9 → ℕ :=
  ![q.childNode,q.parentNode,q.map,q.rowPrefix,q.bitPrefix,q.command,q.source,q.dest,q.count]

def formula : E :=
  let i := v 0; let r := v 1; let s := v 2; let c := v 13
  let rows := pre (v 5) (v 6); let total := add (mul r (v 5)) (mul s (v 6))
  let field (j : ℕ) (x y : E) := eqz c (L j) x y
  field 0 (add (v 11) (mul (L 4) i)) <|
  field 1 (add (v 11) (mul (L 4) (add r s))) <|
  field 2 (add (v 10) (pre (v 3) (v 4))) <| field 3 rows <| field 4 (pre (v 7) (v 8)) <|
  field 5 (add (v 12) (mul (L 5) i)) <| field 6 (add (v 9) (mul (L 4) rows)) <|
  field 7 (add (add (v 9) (mul (L 4) total)) (mul (L 4) rows)) (mul (L 4) (lt i r (v 5) (v 6)))

theorem natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (i r s : ℕ) (A B : BatchRows.Size) (base : Addresses) (col : Fin 9) :
    formula.natural W data mem (args i r s A B base col) = recordWord (BatchRows.record base r s A B i) col := by
  by_cases first : i<r
  · have m : min i r=i := Nat.min_eq_left first.le
    fin_cases col <;>
      simp [formula,args,pre,BatchRows.record,BatchRows.span,recordWord,Formula.natural,natOp,natTest,first,m]
  · have m : min i r=r := Nat.min_eq_right (Nat.le_of_not_gt first)
    fin_cases col <;>
      simp [formula,args,pre,BatchRows.record,BatchRows.span,recordWord,Formula.natural,natOp,natTest,first,m]

def program (W : ℕ) : Term W 1 14 := formula.compile (fun _ => 0)

set_option maxRecDepth 4096 in
theorem program_binds (W : ℕ) : (program W).binds ≤ 200 := by rw [program,Formula.binds_compile]; decide

theorem run (W : ℕ) (data : Fin 1 → ℕ) (mem : ℕ → ℕ) (i r s : ℕ) (A B : BatchRows.Size)
    (base : Addresses) (col : Fin 9) (room : formula.Fits W (fun _ => data 0) mem (args i r s A B base col)) :
    (program W).eval (fun j => (data j : Word W)) (fun j => (mem j : Word W))
      (fun j => ((args i r s A B base col j : ℕ) : Word W)) = (recordWord (BatchRows.record base r s A B i) col : Word W) := by
  simp only [program,Formula.eval_compile,Function.comp_def]
  exact (Formula.value_eq_natural formula (fun _ => data 0) mem _ room).trans
    (congrArg (fun q : ℕ => (q : Word W)) (natural W (fun _ => data 0) mem i r s A B base col))

end ThreeFlat.RAM.HistoryBatchProgram

end OAI
