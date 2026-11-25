import OAI.ThreeFlat.Diagonal.RefreshFormulaWork
import OAI.ThreeFlat.RAM.NavigationNodeRowProgram

namespace OAI
/-! # The size of the physical charge calculation is independent of bank addresses -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM RAM.PhysicalPinsExpr RAM.NavigationNodeRows
private def rowAt (b : Banks) : Formula 1 := .op .div (.cut (.reg 0) (NavigationNodeRows.h b 0)) (.lit 2)

private theorem sum_work {I : Type} (l : List I) {f g : I→Formula 1}
    (entry : ∀i,(f i).work=(g i).work) :
    (MotifRows.totals (l.map f)).work=(MotifRows.totals (l.map g)).work :=
  (RefreshDemandRows.Static.folds l f g entry).1

theorem charge_work (b d : Banks) (c h m : ℕ) :
    (charge b c h m).work=(charge d c h m).work := by
  have child (col : ℕ) : (fromChildren b (rowAt b) c col).work=(fromChildren d (rowAt d) c col).work := by
    unfold fromChildren
    apply sum_work
    intro i
    rfl
  have incident : (incidentWidth b (rowAt b) h).work=(incidentWidth d (rowAt d) h).work := by
    unfold incidentWidth
    apply sum_work
    intro i
    rfl
  have motif : (motifCopies b (rowAt b) m).work=(motifCopies d (rowAt d) m).work := by
    change _+_+_+(MotifRows.totals _).work+1=_+_+_+(MotifRows.totals _).work+1
    congr 2
    apply sum_work
    intro i
    rfl
  simp only [rowAt] at child incident motif
  simp only [charge,MotifRows.plus,Formula.work]
  rw [child 0,child 1,incident,motif]
  all_goals rfl

end ThreeFlat.Diagonal.NavigationPass

end OAI
