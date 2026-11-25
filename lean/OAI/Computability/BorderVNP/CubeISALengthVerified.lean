import OAI.Computability.BorderVNP.CubeISALengthImage
import OAI.Computability.BorderVNP.CubeISALengthColumns

/-! # Distributed declaration checks with untrusted public totals

Each pair can verify its own row. The common public scan checks the natural
column sums of all advertised rows, including padding, before it checks the
minimum. Therefore any tuple of passing local checks and any passing public
check force the unique physical declaration and every auxiliary total word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeLengths

open VPVNP.BurstRAM VPVNP.MotifBase Cube Cube.Physical Finset

variable {n d blocks K h : ℕ}

/-- The physical row-major column sum counts each unordered row exactly once. -/
theorem StoredRows.column_sum {l : Layout} {mem : ℕ → ℕ} {rows : Sym2 (Fin d) → Fin (n+1) → ℕ}
    (image : StoredRows mem l.claimed rows) (dim : l.coordinates = n+1) (j : Fin (n+1)) :
    columnPrefix l mem j.val (d*d) = ∑ r, rows r j := by
  classical
  let sorted (p : Fin d × Fin d) := p.1 ≤ p.2
  let value (p : Fin d × Fin d) := rows (Sym2.mk p.1 p.2) j
  let rowValue (k : Fin (d*d)) := mem (l.claimed+(k.val*l.coordinates+j.val))
  have hit (p : Fin d × Fin d) : rowValue (finProdFinEquiv p) =
      if sorted p then value p else 0 := by
    have offset : (entryOrder d (n+1) (p,j)).val = (finProdFinEquiv p).val*l.coordinates+j.val := by
      rw [dim]
      change j.val + (n+1)*(finProdFinEquiv p).val = (finProdFinEquiv p).val*(n+1)+j.val
      ac_rfl
    simpa only [rowValue,← offset] using image p.1 p.2 j
  calc
    columnPrefix l mem j.val (d*d) = ∑ k, rowValue k :=
      (Fin.sum_univ_eq_sum_range (fun k => mem (l.claimed+(k*l.coordinates+j.val))) (d*d)).symm
    _ = ∑ p, rowValue (finProdFinEquiv p) := (Equiv.sum_comp finProdFinEquiv rowValue).symm
    _ = ∑ p, if sorted p then value p else 0 := sum_congr rfl (fun p _ => hit p)
    _ = ∑ p : {p // sorted p}, value p.val := by
      rw [← sum_filter, sum_subtype (p := sorted) (univ.filter sorted) (fun _ => by simp) value]
    _ = ∑ r, rows r j := Fintype.sum_equiv Sym2.sortEquiv.symm _ _ fun _ => rfl

/-- Public acceptance pins every auxiliary total word to the actual declared
column sum, and selects the exact first minimum of these mathematical sums. -/
theorem public_iff {l : Layout} {mem : ℕ → ℕ} {D : LengthDeclaration n d}
    (stored : StoredRows mem l.claimed D.2) (dim : l.coordinates = n+1) (index : l.chosen = D.1.val) :
    ColumnsAgree l mem (d*d) ∧ Least l mem ↔
      (∀ j : Fin (n+1), mem (l.totals+j.val) = ∑ r, D.2 r j) ∧
      D.1 = firstMinimum (fun j => ∑ r, D.2 r j) := by
  have col : ColumnsAgree l mem (d*d) ↔ ∀ j : Fin (n+1), mem (l.totals+j.val) = ∑ r, D.2 r j := by
    constructor
    · intro ok j
      exact (ok j.val (by rw [dim]; exact j.isLt)).trans (stored.column_sum dim j)
    · intro ok j hj
      let k : Fin (n+1) := ⟨j,dim ▸ hj⟩
      exact (ok k).trans (stored.column_sum dim k).symm
  rw [col,least_iff_first l mem dim,index,Fin.val_inj]
  constructor <;> rintro ⟨table,i⟩ <;> refine ⟨table,?_⟩ <;>
    simpa only [table] using i

/-- Check the columns and minimum on the common declaration, and the actual
pair rows on the recomputed selector data. -/
def verified : RoutingISA.Code := .seq rows publicMinimum

/-- All local rows and the global declaration pass precisely when the paper's
predicate passes and the auxiliary totals equal its forced column sums. This
statement imposes no assumption on the values of the supplied total words. -/
theorem verified_run {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (regs : Bank w) (m : Memory w) (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (D : LengthDeclaration n d) (fit : Fits w (readings pub) (readings m))
    (shape : (layout (readings pub) (readings m)).entries = d*d*(n+1))
    (dim : (layout (readings pub) (readings m)).coordinates = n+1)
    (index : (layout (readings pub) (readings m)).chosen = D.1.val)
    (actual : StoredRows (readings m) (layout (readings pub) (readings m)).actual
      (Cube.subtotals itemRow (crossCount b s select) D.1))
    (declared : StoredRows (readings m) (layout (readings pub) (readings m)).claimed D.2) :
    let l := layout (readings pub) (readings m)
    TestRun pub mac verified regs m
      (rowSetup.slots + d*d*(n+1)*(rowBody.slots+1)+1 +
        (columnSetup.slots+(n+1)*(columnCost (d*d)+1)+1 +
          (minSetup.slots+pivot.slots+(n+1)*(minBody.slots+1)+2)))
      (passesLengths b s select D ∧ ∀ j : Fin (n+1), readings m (l.totals+j.val) = ∑ r, D.2 r j)
      (Kept (readings regs) (readings m)) := by
  let l := layout (readings pub) (readings m)
  have row : RowsAgree l (readings m) ↔ ∀ r j, D.2 r j = Cube.subtotals itemRow (crossCount b s select) D.1 r j :=
    rowsAgree_iff l (readings m) shape actual declared
  have stage (t : Bank w) (mt : Memory w) (kept : Kept (readings regs) (readings m) (.ofWords t mt)) := by
    have hm : readings mt = readings m := kept.1
    have shape' : (layout (readings pub) (readings mt)).entries =
        d*d*(layout (readings pub) (readings mt)).coordinates := by rw [hm,shape,dim]
    have pos : 0 < (layout (readings pub) (readings mt)).coordinates := by rw [hm,dim]; omega
    have run := publicMinimum_run (mac := mac) t mt (hm ▸ fit) (d*d) shape' pos
    refine run.mono (ok' := ColumnsAgree l (readings m) (d*d) ∧ Least l (readings m))
      (Q := Kept (readings regs) (readings m))
      (cost' := columnSetup.slots+(n+1)*(columnCost (d*d)+1)+1 +
          (minSetup.slots+pivot.slots+(n+1)*(minBody.slots+1)+2))
      (by rw [hm,dim]) (by rw [hm]) ?_
    intro z hz
    exact ⟨hz.1.trans hm,fun j hj => (hz.2 j hj).trans (kept.2 j hj)⟩
  apply ((rows_run regs m fit).seq stage).mono (by rw [shape]) ?_ (fun _ hp => hp)
  rw [row,public_iff declared dim index]
  change (_ ∧ (_ ∧ _)) ↔ (_ ∧ _) ∧ _
  tauto

end RoutingISA.CubeLengths

end BorderVNP
end Computability
end OAI
