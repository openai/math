import OAI.Computability.VPVNP.CompressorGreedyVisitWalk
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-! # Reads of the six greedy launch recipes

The recipes use the pitch word, three scalar fields, three old incidence
heads, and the selected table head. The locations are computed relative to
the first level of the block at the actual visit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyVisit

open BurstRAM PhaseRecipe BlockPlanner DescriptorSpace Greedy
open scoped Fin.CommRing
open private firstRecord recordsEnd controls prepare read projectionParams from
  OAI.Computability.VPVNP.CompressorGreedyLevelPlan

variable {w : ℕ}

theorem planner_reads (D : ℕ → Prop) (pub : Fin 5 → Word w) (s : Word w) (mem : Memory w)
    (F : Shape) (step a : ℕ) (origin : Expr)
    (vert : (LevelFields.vertices step).ReadsFrom D pub s mem)
    (degree : (LevelFields.degree step).ReadsFrom D pub s mem)
    (resid : (LevelFields.residualLanes step).ReadsFrom D pub s mem)
    (inc : ∀ j : Fin 6, (LevelFields.incidence F step j).ReadsFrom D pub s mem)
    (base : origin.ReadsFrom D pub s mem) (j : Stage) :
    HeaderOperands.Supported D pub s mem (visit F step a origin j) := by
  have first (l : Expr) (hl : l.ReadsFrom D pub s mem) : (firstRecord step l).ReadsFrom D pub s mem := ⟨hl,vert⟩
  have ending (width : ℕ) (l : Expr) (hl : l.ReadsFrom D pub s mem) :
      (recordsEnd step width l).ReadsFrom D pub s mem := ⟨first l hl,vert,trivial⟩
  have off : (GreedyLevelPlan.offsetBase step a origin).ReadsFrom D pub s mem := ending _ _ base
  have shift : (GreedyLevelPlan.shiftBase step a origin).ReadsFrom D pub s mem := ending _ _ off
  have zero : (GreedyLevelPlan.zeroAddress step a origin).ReadsFrom D pub s mem := ⟨shift,vert,degree⟩
  have proj (k : Fin 5) : (projectionParams F step a origin k).ReadsFrom D pub s mem := by
    fin_cases k <;> first | exact inc 2 | exact shift | exact zero | exact resid | trivial
  have init {d : ℕ} (width : ℕ) (rows : OperandRows d) (disps labels z : Expr)
      (hd : disps.ReadsFrom D pub s mem) (hl : labels.ReadsFrom D pub s mem) (hz : z.ReadsFrom D pub s mem) :
      HeaderOperands.Supported D pub s mem (prepare F step width rows disps labels z) := by
    refine ⟨trivial,vert,?_⟩
    intro k
    cases k using Fin.addCases with
    | left i => simp only [prepare, Fin.addCases_left]; trivial
    | right i =>
      simp only [prepare,Fin.addCases_right]
      fin_cases i <;> first | exact degree | exact inc 0 | exact inc 1 | exact hd | exact hl | exact hz | exact first _ hl | trivial
  have reader (k n width : ℕ) (labels : Expr) (hl : labels.ReadsFrom D pub s mem) :
      HeaderOperands.Supported D pub s mem (read step k n width labels) :=
    ⟨first _ hl,ending _ _ hl,fun i => Fin.elim0 i⟩
  cases j with
  | extract => exact ⟨trivial,⟨vert,degree⟩,proj⟩
  | zero => exact ⟨trivial,trivial,proj⟩
  | colorPrepare => exact init _ _ _ _ _ (inc 2) base zero
  | colorRead => exact reader _ _ _ _ base
  | tagPrepare => exact init _ _ _ _ _ shift off zero
  | tagRead => exact reader _ _ _ _ off

/-- When the launch state addresses the correct block, each loaded scalar
is in the data region, and the sole address load below it is the pitch. -/
theorem scalar_support (D : ℕ → Prop) {pub : Fin 5 → Word w} {s : Word w} {mem : Memory w}
    (L : Layout) (first step offset : ℕ) (entry : LevelFields.Entry L first pub s mem)
    (pitch : D (pub 1-1).val) (allowed : D (levelStart L (first+step)+offset))
    (fit : levelStart L (first+step)+offset < 2^w) :
    (LevelFields.scalar step offset).ReadsFrom D pub s mem := by
  refine ⟨⟨⟨trivial,trivial,⟨trivial,trivial⟩,pitch⟩,trivial⟩,?_⟩
  rw [LevelFields.eval_address entry,Fin.val_natCast,Nat.mod_eq_of_lt fit]
  exact allowed

end CompressorRecords.GreedyVisit

end VPVNP
end Computability
end OAI
