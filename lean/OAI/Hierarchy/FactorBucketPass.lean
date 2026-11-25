import OAI.Hierarchy.FactorBucketRAM
import OAI.Hierarchy.GridPassageRAMState
import Mathlib.Tactic.Ring

namespace OAI
/-! # Exact execution and natural-number interpretation of the bucket passes -/

namespace Hierarchy.FactorBucketRAM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {w P R K : ℕ}

def iterRows (step : Parameters w → Word w → Memory w → Memory w) (v : Parameters w)
    (m : Memory w) : ℕ → Memory w
  | 0 => m
  | n+1 => step v (n:Word w) (iterRows step v m n)

/-- All three native blocks run for an exact linear number of clock ticks. -/
theorem advance_rows (ops : List (Op 14 12))
    (step : Parameters w → Word w → Memory w → Memory w)
    (M : Machine w P R K) (pc : Fin (3+ops.length) ↪ Fin P) (reg : Fin 14 ↪ Fin R)
    (pub : Fin 12 → Fin K) (exit : Fin P)
    (installed : (OrdinalOpLoop.block w ops 0 1 0).Installed M pc reg pub exit)
    (n : ℕ) (fit : n<2^w) (count : M.publicData (pub 0)=(n:Word w))
    (rows : ∀ state rs m, Executes ops step reg pub M.publicData state rs m)
    (c : Config w P R) (entry : c.pc=pc (OrdinalOpLoop.block w ops 0 1 0).first)
    (m : Memory w) : ∃ out, advance M.program (3+n*(1+ops.length)) c m =
      some (out,iterRows step (M.publicData ∘ pub) m n) ∧ out.pc=exit := by
  apply OrdinalOpLoop.advance_block ops 0 1 (by decide) 0 M pc reg pub exit installed n fit count
    (iterRows step (M.publicData ∘ pub) m) _ c entry
  intro i _ state rs atRow atBound
  obtain ⟨es,out,h,h₀,h₁⟩ := rows state rs (iterRows step (M.publicData ∘ pub) m i)
  refine ⟨es,out,?_,?_,h₁.trans atBound⟩
  · simpa [iterRows,atRow] using h
  · simpa [atRow] using h₀

private theorem nonzero_bit (a : Word w) :
    BinaryOp.div.eval a a = if a.val=0 then 0 else 1 := by
  by_cases h : a.val=0
  · simp [BinaryOp.eval,h]
  · simp [BinaryOp.eval,h,Nat.div_self (Nat.pos_of_ne_zero h)]

private theorem quotient_flag (x entry : Word w) (positive : 0<entry.val) :
    let ratio := BinaryOp.div.eval x entry
    BinaryOp.div.eval ratio ratio = if entry.val≤x.val then 1 else 0 := by
  have fit : x.val/entry.val < 2^w := (Nat.div_le_self _ _).trans_lt x.isLt
  have val : (BinaryOp.div.eval x entry).val = x.val / entry.val :=
    Nat.mod_eq_of_lt fit
  dsimp only
  rw [nonzero_bit,val]
  by_cases yes : entry.val ≤ x.val
  · simp [yes,Nat.ne_of_gt (Nat.div_pos yes positive)]
  · simp [yes,Nat.div_eq_of_lt (Nat.lt_of_not_ge yes)]

/-- A physical row scanning one threshold publishes the last eligible index,
clearing the digit at the beginning of each new resource. -/
theorem digit_natural (v : Parameters w) (i : Word w) (m : Memory w)
    (row col : ℕ) (rowAt : BinaryOp.div.eval i (v 1) = (row:Word w))
    (colAt : BinaryOp.mod.eval i (v 1) = (col:Word w)) (colFit : col<2^w)
    (resourceBase thresholdBase digitBase : ℕ) (rAt : v 5=(resourceBase:Word w))
    (tAt : v 6=(thresholdBase:Word w)) (dAt : v 7=(digitBase:Word w))
    (rFits : resourceBase+row<2^w) (tFits : thresholdBase+col<2^w)
    (dFits : digitBase+row<2^w) (x : ℕ) (readResource : (m (resourceBase+row)).val=x)
    (readThreshold : (m (thresholdBase+col)).val = FactorBucket.threshold col) :
    digitStep v i m = Function.update m (digitBase+row)
      (if FactorBucket.threshold col≤x then ((col+1:ℕ):Word w)
       else if col=0 then 0 else m (digitBase+row)) := by
  simp only [digitStep,rowAt,colAt,rAt,tAt,dAt,←Nat.cast_add,
    Fin.val_cast_of_lt rFits,Fin.val_cast_of_lt tFits,Fin.val_cast_of_lt dFits]
  rw [GridPassageRAMRow.writeMemory_nat _ _ dFits]
  congr 1
  have hpos : 0<(m (thresholdBase+col)).val := by rw [readThreshold]; exact FactorBucket.threshold_pos _
  rw [quotient_flag _ _ hpos, readThreshold,readResource,nonzero_bit,Fin.val_cast_of_lt colFit]
  by_cases h : FactorBucket.threshold col≤x <;> by_cases z : col=0 <;> simp [h,z]

end Hierarchy.FactorBucketRAM

end OAI
