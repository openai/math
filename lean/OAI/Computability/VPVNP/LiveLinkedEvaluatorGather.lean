import OAI.Computability.VPVNP.LiveLinkedEvaluatorHandoff
import OAI.Computability.VPVNP.LiveConfigGatherRun

/-!
# The two evaluator configuration gathers in the complete live group

On a noninitial tail group the incoming gather hands off to the last-group
router. On a nonfinal group the outgoing gather hands off to the evaluator
transition. In each case the source is the actual bit scratch region and
the continuation receives the packed word bank and the new stage tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorGather

open BurstRAM LiveStageLink PairStages LiveConfigGather
open scoped Fin.CommRing

/-- The two actual rows of the outer table which gather cut configurations. -/
def stage (outgoing : Bool) : Stage := if outgoing then Stage.newGather else Stage.oldGather

/-- The stage reached after a configuration gather, the last-group router for incoming data or
transition checking for outgoing data. -/
def destination (outgoing : Bool) : Stage := if outgoing then Stage.transition else Stage.last

/-- The live configuration-gather operands selecting the left or right cut source and the
corresponding old or new state bank. -/
def operands (G : PairStages.Group) (outgoing : Bool) : Fin 4 → Word G.w :=
  Pieces.word G.g G.lit ∘ InputOperand.geometry ∘
    if outgoing then StageOperands.gather G.constants .right (Layout.newState G.constants)
    else StageOperands.gather G.constants .left (Layout.oldState G.constants)

variable (G : PairStages.Group) (outgoing : Bool) {k : ℕ}

private theorem source_run (fuel : ℕ) (m : Memory G.w) (bs : List (List Bool)) :
    runSegment (Pieces.component G.components (stage outgoing) G.g G.lit) fuel (some 0) m bs =
      runSegment (LiveConfigGather.machine (operands G outgoing)) fuel (some 0) m bs := by cases outgoing <;> rfl

/-- The native word reports for gathering a serialized configuration, in destination-word
order. -/
def reports (bits : Fin (k * G.w) → Bool) : List (Report G.w) :=
  (List.finRange k).map (wordReport (operands G outgoing) ((RAMSerialization.arrayBits k G.w).symm bits))

/-- Conditions on the four physically computed operands and their memory
regions. A separate destination region preserves all unread source bits. -/
structure Fit (k : ℕ) : Prop where
  positive : 0 < k
  width : 2 ≤ G.w
  wordWidth : ((operands G outgoing) 2).val = G.w
  count : ((operands G outgoing) 3).val = k
  source : ((operands G outgoing) 0).val + k * G.w ≤ 2 ^ G.w
  dest : ((operands G outgoing) 1).val + k ≤ 2 ^ G.w
  disjoint : ((operands G outgoing) 0).val + k * G.w ≤ ((operands G outgoing) 1).val ∨
    ((operands G outgoing) 1).val + k ≤ ((operands G outgoing) 0).val
  tagOutside : G.addr.val < ((operands G outgoing) 1).val ∨
    ((operands G outgoing) 1).val + k ≤ G.addr.val

private theorem report_frame (bits : Fin (k * G.w) → Bool) (F : Fit G outgoing k) :
    PreservesTag G.addr (reports G outgoing bits) := by
  intro rep hrep m
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrep
  rw [wordReport, report_memory]
  let base := (operands G outgoing) 1
  have hf := F.dest
  change base.val + k ≤ 2 ^ G.w at hf
  have he : (base + (i.val : Word G.w)).val = base.val + i.val := by
    rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hd := F.tagOutside
  change G.addr.val < base.val ∨ base.val + k ≤ G.addr.val at hd
  exact ite_eq_right (show G.addr.val ≠ (base + (i.val : Word G.w)).val by rw [he]; omega)

private theorem next_stage : G.nextStage (stage outgoing) = some (destination outgoing) := by
  cases outgoing <;> rfl

/-- Remove the entire deterministic gather prefix from an accepting outer
path. Its retained log includes all native reads and writes and all dispatch
and transfer costs, and the tail starts in the actual post-gather memory. -/
noncomputable def handoff (F : Fit G outgoing k) (hclock : 8 * G.w + 67 ≤ G.clock)
    (m : Memory G.w) (bits : Fin (k * G.w) → Bool) (ht : G.tagged (stage outgoing) m)
    (hsrc : ArrayBitImage m ((operands G outgoing) 0) bits) (cap : List (Report G.w) → Prop) :
    let bank := gathered ((operands G outgoing) 1) F.dest bits m
    let logs := G.linkedLogs (stage outgoing) (reports G outgoing bits)
    ActualPaths G.P G.clock 0 (writeMemory bank G.addr (tagWord G.w (destination outgoing)))
      (fun rs => cap (logs ++ rs)) ≃ ActualPaths G.P G.clock 0 m cap := by
  let data := operands G outgoing
  let bank := gathered (data 1) F.dest bits m
  have hr := (run_array data bits F.width F.wordWidth F.count F.positive (fuel := 8*G.w+20) le_rfl
    F.source F.dest F.disjoint m hsrc (List.replicate k []) (reports G outgoing bits) bank).mpr ⟨rfl,rfl,rfl⟩
  exact G.deterministicHandoff (by omega) ht ((report_frame G outgoing bits F).onReturns m)
    (next_stage G outgoing) ((source_run G outgoing ..).trans hr.1) hr.2.1 hr.2.2 cap

/-- Number of reports, native probes, and the unique final transfer all
contribute to the resource accounting of this gather in the outer table. -/
theorem linked_cost (bits : Fin (k * G.w) → Bool) (F : Fit G outgoing k)
    (hclock : 8*G.w+67 ≤ G.clock) (m : Memory G.w) (ht : G.tagged (stage outgoing) m)
    (hsrc : ArrayBitImage m ((operands G outgoing) 0) bits) :
    RAMBuckets.cost Report.probes (G.linkedLogs (stage outgoing) (reports G outgoing bits)) =
      k * (G.w + 3) + 1 := by
  let data := operands G outgoing
  let bank := gathered (data 1) F.dest bits m
  obtain ⟨hr, hh, _⟩ := (run_array data bits F.width F.wordWidth F.count F.positive
    (fuel := 8*G.w+20) le_rfl F.source F.dest F.disjoint m hsrc
    (List.replicate k []) (reports G outgoing bits) bank).mpr ⟨rfl,rfl,rfl⟩
  have hc := (G.component_completion (by omega) ht ((report_frame G outgoing bits F).onReturns m)
    ((source_run G outgoing ..).trans hr) hh).2.2.2
  rw [hc, next_stage]
  have count (xs : List (Fin k)) :
      RAMBuckets.cost Report.probes (xs.map (wordReport data ((RAMSerialization.arrayBits k G.w).symm bits))) =
        xs.length * (G.w+2) := by
    induction xs with
    | nil => simp [RAMBuckets.cost]
    | cons j xs ih =>
      simp only [List.map_cons, RAMBuckets.cost, List.length_cons, ih, wordReport, report_probes, Nat.succ_mul]
      omega
  unfold reports
  rw [count, List.length_map, List.length_finRange]
  simp
  ring

end LiveProgram.EvaluatorGather

end VPVNP
end Computability
end OAI
