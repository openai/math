import OAI.Computability.VPVNP.CompressorShrinkSlotScheduledRuns
import OAI.Computability.VPVNP.CompressorFormulaFootprint

/-!
# Reads of the twenty-two shrinking slot planners

All level-dependent counts and column heads are computed arithmetically
from the seven inputs to the sorted-slot passes. The remaining reads come
from the chosen layout, the split-width head, and the six destination heads.
These are footprints of the planner operands in their entry memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPlan.Scheduled

open BurstRAM PhaseRecipe

variable {w : ℕ}

/-- All expressions from the surrounding block that can supply a slot planner. -/
structure Roots (P : Plan) (data : ℕ → Prop) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) : Prop where
  bases : P.input.bases.ReadsFrom data pub state m
  lanes : P.input.lanes.ReadsFrom data pub state m
  oldArc : P.input.oldArc.ReadsFrom data pub state m
  role : P.input.role.ReadsFrom data pub state m
  subdivisions : P.input.subdivisions.ReadsFrom data pub state m
  nextSite : P.input.nextSite.ReadsFrom data pub state m
  scratch : P.input.scratch.ReadsFrom data pub state m
  chosen : P.layout.ReadsFrom data pub state m
  split : P.split.ReadsFrom data pub state m
  columns : ∀ c, (LevelFields.incidence P.space (P.step+1) c).ReadsFrom data pub state m

variable (P : Plan) {data : ℕ → Prop} {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
local notation "R" => Expr.ReadsFrom data pub state m
local notation "cs" => SlotLevel.Recipe.counts P.template P.input
local notation "os" => ShrinkSlots.Recipe.columns P.template P.input

private structure CountReads (c : SlotLevel.Recipe.Counts Expr) (r : Expr → Prop) : Prop where
  sites : r c.sites
  pad : r c.pad
  oldBaseArcs : r c.oldBaseArcs
  genuineArcs : r c.genuineArcs
  genuine : r c.genuine
  dummy : r c.dummy
  fields : r c.fields
  owners : r c.owners
  baseArcs : r c.baseArcs
  rows : r c.rows
  inverse : r c.inverse
  targets : r c.targets
  shifts : r c.shifts
  stopAddress : r c.stopAddress

private theorem count_reads (h : Roots P data pub state m) : CountReads cs R := by
  have sites : R (cs).sites := ⟨h.bases,trivial,h.lanes⟩
  have old : R (cs).oldBaseArcs := ⟨h.bases,trivial⟩
  have gen : R (cs).genuineArcs := ⟨⟨trivial,old,trivial⟩,h.lanes⟩
  have fields : R (cs).fields := ⟨⟨gen,sites,trivial⟩,trivial⟩
  have owners : R (cs).owners := ⟨sites,trivial⟩
  have arcs : R (cs).baseArcs := ⟨⟨h.bases,trivial⟩,trivial⟩
  have rows : R (cs).rows := ⟨⟨h.scratch,fields⟩,owners,fields⟩
  have inv : R (cs).inverse := ⟨rows,⟨owners,fields⟩,trivial⟩
  have targets : R (cs).targets := ⟨inv,fields⟩
  have shifts : R (cs).shifts := ⟨targets,arcs⟩
  exact ⟨sites,trivial,old,gen,⟨gen,trivial⟩,⟨⟨sites,trivial⟩,trivial⟩,fields,owners,arcs,
    rows,inv,targets,shifts,⟨shifts,arcs⟩⟩

private structure ColumnReads (c : ShrinkSlots.Recipe.Columns) (r : Expr → Prop) : Prop where
  count : r c.count
  baseInverse : r c.baseInverse
  actualOut : r c.actualOut
  actualIn : r c.actualIn
  width : r c.width

private theorem column_reads (h : CountReads cs R) : ColumnReads os R := by
  have count : R (os).count := ⟨h.sites,trivial⟩
  have out : R (os).actualOut := ⟨h.stopAddress,h.baseArcs⟩
  have incoming : R (os).actualIn := ⟨out,count⟩
  exact ⟨count,h.stopAddress,out,incoming,⟨incoming,count⟩⟩

private theorem core_reads (h : Roots P data pub state m) (c : CountReads cs R) (p : SlotLevel.Phase) :
    let v := (.core p : Stage).visit P
    R v.initial ∧ R v.stop ∧ ∀ j, R (v.params j) := by
  intro v
  cases p with
  | genuineOwners =>
    refine ⟨trivial,c.genuine,?_⟩
    intro j; change Fin 8 at j; fin_cases j
    exacts [h.lanes,trivial,c.oldBaseArcs,h.oldArc,h.role,h.subdivisions,c.owners,h.scratch]
  | dummyOwners =>
    refine ⟨trivial,c.dummy,?_⟩
    intro j; change Fin 3 at j; fin_cases j
    exacts [c.pad,h.nextSite,⟨h.scratch,c.genuine⟩]
  | appendFields =>
    refine ⟨trivial,c.fields,?_⟩
    intro j; change Fin 6 at j; fin_cases j
    exacts [c.fields,h.scratch,⟨c.owners,c.fields⟩,⟨h.scratch,c.fields⟩,trivial,c.rows]
  | invertFields =>
    refine ⟨trivial,⟨c.owners,trivial⟩,?_⟩
    intro j; change Fin 2 at j; fin_cases j
    exacts [c.rows,c.inverse]
  | baseMatching =>
    refine ⟨trivial,c.baseArcs,?_⟩
    intro j; change Fin 6 at j; fin_cases j
    exacts [trivial,h.lanes,c.rows,c.inverse,c.targets,c.shifts]

private theorem output_reads (h : Roots P data pub state m) (c : CountReads cs R) (o : ColumnReads os R)
    (p : ShrinkSlots.Recipe.Phase) : let v := (.output p : Stage).visit P
    R v.initial ∧ R v.stop ∧ ∀ j, R (v.params j) := by
  intro v
  cases p with
  | baseInverse =>
    refine ⟨trivial,c.baseArcs,?_⟩
    intro j; change Fin 2 at j; fin_cases j
    exacts [c.targets,o.baseInverse]
  | actualOut =>
    refine ⟨trivial,o.count,?_⟩
    intro j; change Fin 5 at j; fin_cases j
    exacts [trivial,h.lanes,c.targets,c.shifts,o.actualOut]
  | actualIn =>
    refine ⟨trivial,o.count,?_⟩
    intro j; change Fin 5 at j; fin_cases j
    exacts [trivial,h.lanes,o.baseInverse,c.shifts,o.actualIn]
  | widths =>
    refine ⟨trivial,o.count,?_⟩
    intro j; change Fin 8 at j; fin_cases j
    exacts [trivial,h.lanes,trivial,c.oldBaseArcs,c.genuineArcs,c.rows,h.split,o.width]

/-- Every expression in the active worker's chronological operand row reads
only the supplied region. -/
theorem Stage.reads (stage : Stage) (h : Roots P data pub state m) :
    R (stage.visit P).initial ∧ R (stage.visit P).stop ∧ ∀ j, R ((stage.visit P).params j) := by
  have c := count_reads P h
  have o := column_reads P c
  cases stage with
  | subdivision i =>
    refine ⟨trivial,trivial,?_⟩
    intro j; change Fin 2 at j; fin_cases j
    exacts [⟨h.subdivisions,trivial⟩,trivial]
  | roles =>
    refine ⟨trivial,trivial,?_⟩
    intro j; change Fin 2 at j; fin_cases j
    exacts [h.chosen,h.role]
  | cyclic =>
    refine ⟨trivial,c.sites,?_⟩
    intro j; change Fin 3 at j; fin_cases j
    exacts [h.lanes,trivial,h.nextSite]
  | clear => exact ⟨trivial,⟨c.owners,c.fields⟩,fun _ ↦ ⟨h.scratch,c.fields⟩⟩
  | core p => exact core_reads P h c p
  | output p => exact output_reads P h c o p
  | copy i =>
    have num : R (columnCount P.template P.input i) := by
      unfold columnCount; split
      · exact c.baseArcs
      · exact o.count
    have src : R (sourceHeads P.template P.input i) := by
      fin_cases i
      exacts [c.targets,o.baseInverse,c.shifts,o.actualOut,o.actualIn,o.width]
    refine ⟨trivial,num,?_⟩
    intro j; change Fin 3 at j; fin_cases j
    exacts [trivial,src,h.columns i]

end CompressorRecords.ShrinkSlotPlan.Scheduled

end VPVNP
end Computability
end OAI
