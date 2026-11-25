import OAI.Hierarchy.GridThroughSelect
import OAI.Hierarchy.GridTickLens

namespace OAI
/-! # The programmed grid of an actual per-rail simulation schedule -/

namespace Hierarchy.GridThrough.Program
open GridLens
noncomputable section

variable {E : Type} [Fintype E] [LinearOrder E] {k n q d : ℕ}

/-- The line/cell bounds on the scheduled factors give a legal native program
on the same external labels and at the same pin addresses as the assignment. -/
def ofScheduled (A : PinAssignment E k n q d) (width : Fin k → ℕ)
    (count : Fin k → GridTicks.Tick k (n+1) q → ℕ)
    (conservation : ∀ j t, (GridTicks.pairFiber A.direction (fun e => GridTicks.index (A.tick e)) j t).card = count j t)
    (enough : ∀ x j, width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j x)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks x))).card) : GridThrough.Program E n (q*d) width := by
  refine ofUntouched A.direction A.row A.touch width (fun x j => (enough x j).trans ?_) A.data A.data_cell A.data_once
  change _ ≤ (untouchedRails A.direction (fun e => (A.tick e).1) (fun e => some ((A.tick e).1 (A.direction e))) x j).card
  simpa only [Equiv.symm_apply_apply] using GridTicks.available_rails_of_tick_counts A.direction
    (fun e => GridTicks.index (A.tick e)) j (count j) (conservation j) x

/-- The scalar exact interpreter may use `Program.eval_ticks` directly on this physical wiring. -/
theorem ofScheduled_allTouched (A : PinAssignment E k n q d) (width : Fin k → ℕ)
    (count : Fin k → GridTicks.Tick k (n+1) q → ℕ)
    (conservation : ∀ j t, (GridTicks.pairFiber A.direction (fun e => GridTicks.index (A.tick e)) j t).card = count j t)
    (enough : ∀ x j, width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j x)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks x))).card) :
    ∀ e, (ofScheduled A width count conservation enough).touch e ≠ none := by
  intro e
  change some (A.row e (A.direction e)) ≠ none
  simp

/-- A scheduled factor list with conserved pair ownership directly programs the physical grid.
The available catalyst capacity is derived from the actual line and cell loads. -/
def ofFactorSchedule {α : Type*} {m w cap B : ℕ} (A : PinAssignment E k n q d)
    (width : Fin k → ℕ) (reserved : ∀ j, width j ≤ B) (cost : α → Fin m → ℕ)
    (items : List α) (coord : Fin k → Fin m) (hg : 4 ≤ n+1) (hq : 0 < q)
    (bits : ∀ a ∈ items, ∀ i, cost a i ≤ 2^w) (bounded : ∀ a ∈ items, ∀ i, cost a i ≤ cap)
    (total : ∀ j, (items.map (fun a => cost a (coord j))).sum = 2 * (n+1)^(k-1) * B)
    (small : ((20*((w:ℝ)+1)+2)^m * cap) * ((n+1)*q : ℕ) ≤ B/16)
    (conservation : ∀ j t, (GridTicks.pairFiber A.direction (fun e => GridTicks.index (A.tick e)) j t).card =
      ((FactorAllocation.factors w cost items t).map (fun a => cost a (coord j))).sum) :
    GridThrough.Program E n (q*d) width := by
  apply ofScheduled A width (fun j t => ((FactorAllocation.factors w cost items t).map (fun a => cost a (coord j))).sum) conservation
  intro x j
  exact (reserved j).trans (GridTicks.scheduled_line_passages hg hq cost items (coord j)
    bits bounded (total j) small j x).2.2

end
end Hierarchy.GridThrough.Program

end OAI
