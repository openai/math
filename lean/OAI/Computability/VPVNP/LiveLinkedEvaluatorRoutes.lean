import OAI.Computability.VPVNP.LiveLinkedEvaluatorGather
import OAI.Computability.VPVNP.LiveLinkedEvaluatorSentinel
import OAI.Computability.VPVNP.LiveProgramHandoffs

/-!
# From the two tail routers to their evaluator banks

The zero flag of each router selects the corresponding gathered configuration.
A one at the last router selects the accepting sentinel, and a one at the first
router selects the initial state writer. Each pair of stages contributes its
literal ordered reports, including all tag updates, to the transcript cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM LiveStageLink PairStages LiveConfigGather
open scoped Fin.CommRing

variable (G : PairStages.Group)

/-- The first-tail router for incoming preparation or the last-group router for outgoing
preparation. -/
abbrev router (outgoing : Bool) : Router := if outgoing then Router.last else Router.firstTail

/-- Write the selected stage's tag into the physical group's dispatcher cell. -/
def retag (s : Stage) (m : Memory G.w) := writeMemory m G.addr (tagWord G.w s)

theorem tagged_retag (s : Stage) (m : Memory G.w) : G.tagged s (retag G s m) := by
  simp [Group.tagged, retag, writeMemory]

/-- The physical outer report of a router jump to the specified stage through the chosen branch
slot. -/
def jumpReport (r : Router) (i : Fin 3) (dest : Stage) :=
  r.outerReport G.evaluator G.g G.lit (r.jumpReport G.g G.lit i (i.val : Word G.w) dest)

private noncomputable def jump (r : Router) (i : Fin 3) (dest : Stage)
    (target : r.target i = .jump (dest.castLE (by decide)))
    (hclock : 57 ≤ G.clock) (hw : 2 ≤ G.w) (m : Memory G.w) (ht : G.tagged r.stage m)
    (flag : m ((r.data G.g G.lit) 0).val = (i.val : Word G.w)) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (retag G dest m) (fun rs => cap (jumpReport G r i dest :: rs)) ≃
      ActualPaths G.P G.clock 0 m cap := by
  rw [G.program_eq]
  simpa only [retag, jumpReport, flag] using r.jumpEquiv G.constants G.evaluator G.pair G.g G.lit
    G.tagFit hw cap G.clock hclock 0 m i flag ht dest target

/-- A stage-tag update outside the source cut preserves every unpacked bit. -/
theorem image_retag {k : ℕ} (s : Stage) {base : Word G.w} {m : Memory G.w}
    {bits : Fin (k*G.w) → Bool} (h : ArrayBitImage m base bits)
    (outside : G.addr.val < base.val ∨ base.val+k*G.w ≤ G.addr.val) :
    ArrayBitImage (retag G s m) base bits := by
  intro i
  have he : base.val+i.val ≠ G.addr.val := by have := i.isLt; omega
  rw [retag, writeMemory, ite_eq_right he, h]

/-- The memory after routing into the gather, packing the cut bits into the selected state
bank, and transferring to its successor. -/
def gatherMemory {k : ℕ} (outgoing : Bool) (F : EvaluatorGather.Fit G outgoing k)
    (m : Memory G.w) (bits : Fin (k*G.w) → Bool) :=
  retag G (EvaluatorGather.destination outgoing) (gathered (EvaluatorGather.operands G outgoing 1) F.dest bits
    (retag G (EvaluatorGather.stage outgoing) m))

/-- The router jump followed by the linked configuration-word gather reports for the selected
incident side. -/
def gatherLogs {k : ℕ} (outgoing : Bool) (bits : Fin (k*G.w) → Bool) :=
  jumpReport G (router outgoing) 0 (EvaluatorGather.stage outgoing) ::
    G.linkedLogs (EvaluatorGather.stage outgoing) (EvaluatorGather.reports G outgoing bits)

/-- The full zero-flag route, including the gathered word array and the
transfer to the last router or terminal transition. -/
noncomputable def gatherHandoff {k : ℕ} (outgoing : Bool) (F : EvaluatorGather.Fit G outgoing k)
    (hclock : 8*G.w+67 ≤ G.clock) (m : Memory G.w) (bits : Fin (k*G.w) → Bool)
    (ht : G.tagged (router outgoing).stage m) (flag : m (((router outgoing).data G.g G.lit) 0).val = 0)
    (img : ArrayBitImage m (EvaluatorGather.operands G outgoing 0) bits)
    (fresh : G.addr.val < (EvaluatorGather.operands G outgoing 0).val ∨
      (EvaluatorGather.operands G outgoing 0).val+k*G.w ≤ G.addr.val) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (gatherMemory G outgoing F m bits)
      (fun rs => cap (gatherLogs G outgoing bits ++ rs)) ≃ ActualPaths G.P G.clock 0 m cap := by
  have route : (router outgoing).target 0 = .jump ((EvaluatorGather.stage outgoing).castLE (by decide)) := by
    cases outgoing <;> rfl
  exact (EvaluatorGather.handoff G outgoing F hclock _ bits (tagged_retag ..)
    (image_retag G _ img fresh) _).trans (jump G _ 0 _ route (by omega) F.width m ht flag cap)

/-- The memory after routing into an endpoint writer, storing the control word, and setting the
next stage tag. -/
def putMemory (outgoing : Bool) (m : Memory G.w) :=
  EvaluatorSentinel.transferred G outgoing (retag G (EvaluatorSentinel.stage outgoing) m)

/-- The router jump and linked control-write report for preparing an evaluator endpoint. -/
def putLogs (outgoing : Bool) :=
  jumpReport G (router outgoing) 1 (EvaluatorSentinel.stage outgoing) ::
    G.linkedLogs (EvaluatorSentinel.stage outgoing) [EvaluatorSentinel.report G outgoing]

/-- The full one-flag route writes the endpoint state and enters the next
live row with cursor zero. This includes the first group's empty evaluator. -/
noncomputable def putHandoff (outgoing : Bool) (hw : 2 ≤ G.w) (hclock : 57 ≤ G.clock)
    (m : Memory G.w) (ht : G.tagged (router outgoing).stage m)
    (flag : m (((router outgoing).data G.g G.lit) 0).val = 1) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (putMemory G outgoing m)
      (fun rs => cap (putLogs G outgoing ++ rs)) ≃ ActualPaths G.P G.clock 0 m cap := by
  have route : (router outgoing).target 1 = .jump ((EvaluatorSentinel.stage outgoing).castLE (by decide)) := by
    cases outgoing <;> rfl
  exact (EvaluatorSentinel.handoff G outgoing (by omega) _ (tagged_retag ..) _).trans
    (jump G _ 1 _ route hclock hw m ht flag cap)

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
