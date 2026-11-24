import OAI.Computability.VPVNP.LiveProgramHeaderFlags
import OAI.Computability.VPVNP.LiveProgramHeader
import OAI.Computability.VPVNP.LiveProgramPairStages

/-!
# Physical header path equivalences for pair and evaluator groups

The same code recovers the actual literals and cut payloads and decides the
mode. At a valid active group the entire choice-free prefix is forced on
every accepting path. Its continuation begins at nomination or at the
first-tail test, with the checked payloads in their physical memory banks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Header
open BurstRAM LiveHeaderProgram LiveHeaderSchedule LiveHeader ChainAssignments PairStages
open scoped Fin.CommRing

/-- A checked finite prefix ending at a named outer stage. -/
structure PrefixTrace (G : Group) (m : Memory G.w) (s : Stage) (count budget : ℕ) where
  /-- Chronological reports of the deterministic header calls that reach the stated outer
  stage. -/
  logs : List (Report G.w)
  run : runSegment G.P G.clock (some 0) m (List.replicate count []) = some logs
  state : endState (some 0) logs = some 0
  tag : G.tagged s (after m (eventLog logs))
  length : logs.length = count
  cost : RAMBuckets.cost Report.probes logs ≤ budget
  probes : ∀ r ∈ logs, r.probes ≤ 10

namespace PrefixTrace
variable {G : Group} {m : Memory G.w} {s : Stage} {n budget : ℕ}

/-- Every accepting path from the original physical memory has exactly these
header bursts. The predicate on the remaining path accounts for their cost. -/
noncomputable def equiv (h : PrefixTrace G m s n budget) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (after m (eventLog h.logs)) (fun rs => cap (h.logs++rs)) ≃
      ActualPaths G.P G.clock 0 m cap := by
  have e := emptySegmentEquiv h.run cap
  rw [h.state] at e
  exact e

end PrefixTrace

variable (G : Group) (hw : 4 ≤ G.g.w) (fuel : 154 ≤ G.clock)
variable (advice : CutSchedule.Bits (sizes G.constants G.g).advice)
variable (cuts : AllCuts (sizes G.constants G.g).h (sizes G.constants G.g).delta)
variable (i : Fin (2^((sizes G.constants G.g).h+1)))
variable (bounds : Fields.Bounds (sizes G.constants G.g) (base G.g) G.g.d G.g.w)
variable (hi : (sizes G.constants G.g).h+2 ≤ 2^G.g.d) (had : (sizes G.constants G.g).advice ≤ 2^G.g.d)
variable (ht : LiveHeaderSchedule.stages.length ≤ 2^G.g.w)
include fuel bounds hi had ht

/-- The deterministic physical prefix up to the mode router, with the exact
header image that the three subsequent cases consume. -/
theorem valid_prefix_equiv (tag : Mode.Tag) (hmode : physicalTag cuts i = some tag)
    (pad : ∀ side, Fields.ValidPadding (sizes G.constants G.g) cuts i tag side) :
    let s := sizes G.constants G.g
    let m := physicalMemory (d := G.g.d) hw advice cuts i
    ∃ h : PrefixTrace G m Stage.mode (callBound s) (costBound s),
      Output s (base G.g) G.g.d hw advice cuts i tag (after m (eventLog h.logs)) := by
  obtain ⟨logs,run,state,out,tagged,len,cost,probes⟩ := valid_prefix G.constants G.evaluator G.pair G.g
    G.lit G.clock hw advice cuts i tag bounds hi had ht fuel hmode pad
  exact ⟨⟨logs,G.program_eq ▸ run,state,tagged,len,cost,probes⟩,out⟩

/-- The two modes in which a checked group continues computation, either counting a primed pair
or checking an evaluator transition. -/
inductive ActiveMode where | pair | tail deriving DecidableEq

/-- The header mode tag for the active pair or evaluator-tail branch. -/
def ActiveMode.tag : ActiveMode → Mode.Tag | .pair => .pair | .tail => .tail
/-- Numeric flag read by the mode router, one for a pair group and two for an evaluator-tail
group. -/
def ActiveMode.flag : ActiveMode → Fin 3 | .pair => 1 | .tail => 2
/-- First continuation after the mode router, the nomination stage for a pair or the first-tail
test for an evaluator group. -/
def ActiveMode.stage : ActiveMode → Stage | .pair => Stage.nominations | .tail => Stage.firstTail

/-- Start the actual nominated pair computation or the evaluator-tail
computation, after the header and mode router have both run. -/
theorem active_prefix (active : ActiveMode) (hmode : physicalTag cuts i = some active.tag)
    (pad : ∀ side, Fields.ValidPadding (sizes G.constants G.g) cuts i active.tag side) :
    let s := sizes G.constants G.g
    let m := physicalMemory (d := G.g.d) hw advice cuts i
    ∃ h : PrefixTrace G m active.stage (callBound s+1) (costBound s+4),
      Output s (base G.g) G.g.d hw advice cuts i active.tag (after m (eventLog h.logs)) := by
  let s := sizes G.constants G.g
  let m := physicalMemory (d := G.g.d) hw advice cuts i
  obtain ⟨h,out⟩ := valid_prefix_equiv G hw fuel advice cuts i bounds hi had ht active.tag hmode pad
  let mem := after m (eventLog h.logs)
  let r := Router.mode
  let flag := mem ((r.data G.g G.lit) 0).val
  let rep := r.outerReport G.evaluator G.g G.lit (r.jumpReport G.g G.lit active.flag flag active.stage)
  have readback : flag = (active.flag.val : Word G.w) := by
    have H := HeaderFlags.mode G.constants G.g G.lit bounds.fit out
    cases active <;> exact H
  have route : r.target active.flag = .jump (active.stage.castLE (by decide)) := by cases active <;> rfl
  have call : BurstRAM.execute G.P G.clock (G.P.start 0) mem [] = some rep := by
    rw [G.program_eq]
    exact r.jump_call G.constants G.evaluator G.pair G.g G.lit G.tagFit (by omega) G.clock (by omega) 0 mem active.flag readback h.tag _ route
  have hrun : runSegment G.P G.clock (some 0) m (List.replicate (callBound s+1) []) = some (h.logs++[rep]) := by
    rw [List.replicate_add,PrimedSchedule.runSegment_append,h.run]
    simp only [Option.bind_some,h.state,show List.replicate 1 ([] : List Bool) = [[]] by rfl]
    change (runSegment G.P G.clock (some 0) mem [[]]).map (h.logs++·) = _
    simp [runSegment,call]
  have post : after m (eventLog (h.logs++[rep])) = writeMemory mem G.addr (LiveStageLink.tagWord G.w active.stage) := by
    have hafter : after m (eventLog (h.logs++[rep])) = after mem rep.events := by
      simp [mem,eventLog,after,List.foldl_append]
    exact hafter.trans (r.after_jump G.evaluator G.g G.lit mem active.flag flag active.stage)
  have hp : rep.probes = 3 := r.outer_jump_probes G.evaluator G.g G.lit active.flag flag active.stage
  have hva := addr_value G.g G.lit G.constants bounds.fit.le
  have hh : G.addr.val < base G.g := by change (addr G.g G.lit).val < 2^G.g.d+1; omega
  refine ⟨⟨h.logs++[rep],hrun,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [endState_append,h.state]; rfl
  · change after m (eventLog (h.logs++[rep])) G.addr.val = _
    rw [post]; simp [writeMemory]
  · simp [h.length]
  · rw [RAMBuckets.cost_append]; simp [RAMBuckets.cost,hp]; exact h.cost
  · intro a ha
    obtain ha | ha := List.mem_append.mp ha
    · exact h.probes a ha
    · obtain rfl := List.mem_singleton.mp ha; omega
  · change Output s (base G.g) G.g.d hw advice cuts i active.tag (after m (eventLog (h.logs++[rep])))
    rw [post]
    exact out.write_outer _ _ hva.ge hh

end LiveProgram.Header

end VPVNP
end Computability
end OAI
