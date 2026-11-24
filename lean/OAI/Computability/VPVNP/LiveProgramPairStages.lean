import OAI.Computability.VPVNP.LiveProgramSchedule
import OAI.Computability.VPVNP.LiveDeterministicPaths

/-! # Native first-half stage completions at a common group clock

The dispatcher has a different length at each tag. Subtracting that length
from one group clock gives the source clock of the selected stage. The
continuation receives the actual transferred memory and the accumulated
report cap, including the dispatch and transfer probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages

open BurstRAM BurstRAM.PrivateRAM LiveStageLink
open scoped Classical

/-- A live group with its fixed components, physical geometry and literal prefix, common call
clock, and bounds ensuring that stage tags and dispatch fit. -/
structure Group where
  /-- Fixed parameters for the grammar, motif labels, header capacities, and evaluator windows. -/
  constants : Constants
  /-- The universal evaluator program used in the group’s component table and stage
  transitions. -/
  evaluator : UniversalMachine.Program
  /-- The pair instruction table mounted at the group’s pair stage. -/
  pair : PairTable
  /-- Physical input length, address width, bucket capacity, and RAM word width for the group. -/
  g : Geometry
  /-- Literal prefix whose packed value and length can supply public operands. -/
  lit : LiteralPrefix
  /-- Common fuel allowance for a linked group call, including outer dispatch. -/
  clock : ℕ
  tagFit : 21 ≤ 2^g.w
  dispatchFit : 44 ≤ clock

namespace Group

variable (G : Group)

/-- RAM word width of this group’s physical geometry. -/
abbrev w := G.g.w
/-- Component rows assembled from the fixed constants, evaluator program, and pair table. -/
abbrev components := rows G.constants G.evaluator G.pair
/-- Linked private instruction template containing all of the group’s component rows. -/
abbrev T := Pieces.table G.components
/-- Public operand words of the linked table, obtained from the geometry and actual literal
prefix. -/
abbrev pub := Pieces.word G.g G.lit ∘ Pieces.bank G.components
/-- The group’s dispatch-tag address encoded as a RAM word. -/
abbrev addr := Pieces.word G.g G.lit (.geometry Layout.stageTag)
/-- Successor-stage function for the group’s evaluator program. -/
abbrev nextStage := next G.evaluator
/-- Outer dispatcher program with the linked components, successor stages, public operands, and
actual tag address. -/
abbrev P := outerProgram G.T G.nextStage G.pub G.addr
/-- Fuel left for a source-stage call after charging the dispatch events for its selected tag. -/
abbrev clockAt (s : Stage) := G.clock - (dispatchEvents G.addr s).length
/-- Complete ordinary source histories starting in state zero at the supplied memory, with the
selected stage’s residual fuel and linked-report room checks. -/
abbrev StagePaths (s : Stage) (m : Memory G.w) := Ordinary G.T G.nextStage G.pub G.addr s (G.clockAt s) 0 m
/-- The memory at the group’s tag address contains the word encoding the selected stage. -/
abbrev tagged (s : Stage) (m : Memory G.w) := m G.addr.val = tagWord G.w s

theorem clock_add (s : Stage) : G.clockAt s + (dispatchEvents G.addr s).length = G.clock := by
  have h := G.dispatchFit
  have hlen : (dispatchEvents G.addr s).length ≤ 44 := by
    simp only [dispatchEvents,List.length_cons,List.length_replicate]
    have hs := s.isLt
    omega
  exact Nat.sub_add_cancel (hlen.trans h)

/-- The program with flattened, stage-relocated operands is the physical group program. -/
theorem program_eq : G.P = (LiveProgram.machine G.constants G.evaluator G.pair G.g G.lit).program := by
  unfold LiveProgram.machine Pieces.machine Pieces.program
  rw [Pieces.data_eq]
  rfl

variable {G}

/-- Entry certificate for a tagged stage. Its invariant holds at state zero and supplies the
tag-preservation condition for the stage’s returns. -/
structure Entry (G : Group) (s : Stage) (m : Memory G.w) where
  /-- Invariant on the returned state word and memory used to establish the stage’s tag frame. -/
  inv : Word G.w → Memory G.w → Prop
  frame : TagFrame G.T G.pub G.addr s (G.clockAt s) inv
  ready : inv 0 m
  tag : G.tagged s m

/-- The ordinary stage traces indexed by their mathematical choices. -/
structure Indexed (G : Group) (s : Stage) (m : Memory G.w) (ι : Type*) extends Entry G s m where
  /-- Bijection between the chosen indices and complete ordinary source histories of the stage. -/
  traces : ι ≃ G.StagePaths s m

namespace Indexed

variable {s : Stage} {m : Memory G.w} {ι : Type*} (A : Indexed G s m ι)

/-- Map the indexed history’s ordinary reports to their linked reports, including outer
dispatch and stage transfer. -/
noncomputable def logs (x : ι) : List (Report G.w) :=
  (ordinaryReports (A.traces x)).map (linkedReport G.nextStage G.addr s)

/-- Memory after the indexed history’s source events and transfer to its successor stage. -/
noncomputable def memory (x : ι) : Memory G.w :=
  transferMemory G.addr (G.nextStage s) (after m (eventLog (ordinaryReports (A.traces x))))

/-- The transferred tag of an ordinary stage is visible on entry to its successor. -/
theorem tagged_memory {s' : Stage} (hnext : G.nextStage s = some s') (x : ι) : G.tagged s' (A.memory x) := by
  change transferMemory G.addr _ _ G.addr.val = _
  simp [transferMemory,hnext,writeMemory]

/-- A completed component indexed by its own branch data, followed by an
arbitrary native continuation at the same outer clock. -/
noncomputable def continuationEquiv {s' : Stage} (hnext : G.nextStage s = some s')
    (cap : List (Report G.w) → Prop) :
    (Σ x : ι, ActualPaths G.P G.clock 0 (A.memory x) (fun rest => cap (A.logs x ++ rest))) ≃
      ActualPaths G.P G.clock 0 m cap := by
  let e := ordinaryEquiv (next := G.nextStage) (cap := cap) G.tagFit A.frame A.ready A.tag
  have htime := G.clock_add s
  refine (Equiv.sigmaCongr (β₂ := fun p : G.StagePaths s m => Remainder cap p) A.traces (fun x => ?_)).trans ?_
  · change _ ≃ Remainder cap (A.traces x)
    unfold Remainder memory logs
    rw [htime,transferState,hnext]
    exact Equiv.refl _
  · simpa only [htime] using e

end Indexed
end Group
end LiveProgram.PairStages

end VPVNP
end Computability
end OAI
