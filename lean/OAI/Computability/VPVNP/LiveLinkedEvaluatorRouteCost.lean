import OAI.Computability.VPVNP.LiveOutsideTailStages
import OAI.Computability.VPVNP.LiveLinkedEvaluatorCount

/-!
# Costs of the incoming and outgoing routes to the evaluator

The zero-flag route makes one router jump followed by one gather call per
configuration word. The one-flag route makes a jump and a control-word
write. In both cases the charged reports include the stage dispatcher and
its transfer to the next row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM LiveStageLink PairStages LiveEvaluatorEncoding
open scoped Fin.CommRing

variable (G : Group) {k M : ℕ}

theorem gatherLogs_cost (outgoing : Bool) (bits : Fin (k*G.w) → Bool) :
    RAMBuckets.cost Report.probes (gatherLogs G outgoing bits) ≤ 4+k*(G.w+4) := by
  simpa only [Nat.mul_comm k (G.w+4)] using (OutsideTailStages.gatherRoute G outgoing bits).cost

/-- The gather reads the bits of one word and writes the reconstructed word.
The linked route adds at most two probes to each such report. -/
theorem gatherLogs_calls (outgoing : Bool) (bits : Fin (k*G.w) → Bool) :
    ∀ r ∈ gatherLogs G outgoing bits, 1+r.probes ≤ G.w+4 := by
  rw [gatherLogs, List.forall_mem_cons]
  constructor
  · have hp := (router outgoing).outer_jump_probes G.evaluator G.g G.lit 0
      ((0 : Fin 3).val : Word G.w) (EvaluatorGather.stage outgoing)
    change (jumpReport G (router outgoing) 0 (EvaluatorGather.stage outgoing)).probes = 3 at hp
    rw [hp]; omega
  · intro rep hrep
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hrep
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hraw
    have hp : (LiveConfigGather.wordReport (EvaluatorGather.operands G outgoing)
      ((RAMSerialization.arrayBits k G.w).symm bits) i).probes = G.w+1 := LiveConfigGather.report_probes ..
    rw [linkedReport_probes, hp]
    split <;> omega

private theorem put_probes (outgoing : Bool) :
    (linkedReport G.nextStage G.addr (EvaluatorSentinel.stage outgoing) (EvaluatorSentinel.report G outgoing)).probes = 3 := by
  rw [linkedReport_probes]
  have nextSome : (G.nextStage (EvaluatorSentinel.stage outgoing)).isSome := by
    cases outgoing with
    | true => rfl
    | false =>
      change (if G.evaluator.extra = 0 then some Stage.last else some Stage.prefixLength).isSome = true
      split <;> rfl
  rw [ite_eq_left ⟨rfl, nextSome⟩]
  rfl

/-- Each endpoint path consists of two four-unit calls. -/
theorem putLogs_cost (outgoing : Bool) : RAMBuckets.cost Report.probes (putLogs G outgoing) = 8 := by
  have hj := (router outgoing).outer_jump_probes G.evaluator G.g G.lit 1
    ((1 : Fin 3).val : Word G.w) (EvaluatorSentinel.stage outgoing)
  change (jumpReport G (router outgoing) 1 (EvaluatorSentinel.stage outgoing)).probes = 3 at hj
  simp only [putLogs, Group.linkedLogs, List.map_singleton, RAMBuckets.cost, hj, put_probes]

theorem putLogs_calls (outgoing : Bool) :
    ∀ r ∈ putLogs G outgoing, 1+r.probes = 4 := by
  have hj := (router outgoing).outer_jump_probes G.evaluator G.g G.lit 1
    ((1 : Fin 3).val : Word G.w) (EvaluatorSentinel.stage outgoing)
  change (jumpReport G (router outgoing) 1 (EvaluatorSentinel.stage outgoing)).probes = 3 at hj
  simp [putLogs, Group.linkedLogs, hj, put_probes]

namespace Output

variable {G} {m : Memory G.w} {b : Option (Code G.evaluator.extra M)}

/-- Either kind of outgoing field fits the word-gather allowance. -/
theorem logs_cost (o : Output G m b) :
    RAMBuckets.cost Report.probes o.logs ≤ 4+fieldWords M*(G.w+4) := by
  cases o with
  | cut _ bits => exact gatherLogs_cost G true bits
  | final =>
    change RAMBuckets.cost Report.probes (putLogs G true) ≤ _
    rw [putLogs_cost]
    have h : 1 ≤ fieldWords M := by unfold fieldWords; omega
    have h' := Nat.mul_le_mul_right (G.w+4) h
    rw [Nat.one_mul] at h'
    omega

theorem logs_calls (o : Output G m b) : ∀ r ∈ o.logs, 1+r.probes ≤ G.w+4 := by
  cases o with
  | cut _ bits => exact gatherLogs_calls G true bits
  | final =>
    intro r hr
    have := putLogs_calls G true r hr
    omega

end Output

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
