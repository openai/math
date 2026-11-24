import OAI.Computability.VPVNP.LiveLinkedEvaluatorHandoff
import OAI.Computability.VPVNP.LiveEvaluatorInitializeStages

/-!
# Native control-word writes at evaluator endpoints

The first group writes its initial state and the last group writes the accepting
state. Both single-call stages have a unique empty choice string. They enter the
next row of the actual live program with an updated control word and stage tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorSentinel

open BurstRAM LiveStageLink PairStages LiveEvaluatorInitialize LiveEvaluatorEncoding
open scoped Fin.CommRing

variable (G : PairStages.Group)

/-- Select the initial-state or final-state control writer for the corresponding endpoint. -/
def stage (final : Bool) : Stage := if final then Stage.finalState else Stage.initialState

/-- The successor of the endpoint writer, accounting for a halted initial evaluator and for
prefix preparation on a running one. -/
def destination (final : Bool) : Stage := if final then Stage.transition else
  if G.evaluator.extra = 0 then Stage.last else Stage.prefixLength

/-- The evaluator control word to install, accepting at the final endpoint or giving the
program's initial control state. -/
def tag (final : Bool) : Word 2 := if final then 1 else controlTag G.evaluator

/-- The public control-write operands selecting the old state bank at the start or the new
state bank at the end. -/
def operands (final : Bool) : Fin 4 → Word G.w := Pieces.word G.g G.lit ∘ InputOperand.geometry ∘
  StageOperands.control G.constants (if final then Layout.newState G.constants else Layout.oldState G.constants)

/-- The terminating source report that writes the endpoint control word after two local steps. -/
def report (final : Bool) : Report G.w :=
  ⟨[.tick, .tick, .write (operands G final 1) (Fin.ofNat _ (tag G final).val)], none⟩

/-- Store the endpoint control tag at the selected state bank's control-word address. -/
def put (final : Bool) (m : Memory G.w) :=
  writeMemory m (operands G final 1) (Fin.ofNat _ (tag G final).val)

/-- The endpoint-writer memory after the enclosing linker also writes the destination stage
tag. -/
def transferred (final : Bool) (m : Memory G.w) := writeMemory (put G final m) G.addr (tagWord G.w (destination G final))

private theorem next_stage (final : Bool) : G.nextStage (stage final) = some (destination G final) := by
  cases final
  · change (if G.evaluator.extra = 0 then some Stage.last else some Stage.prefixLength) = _
    by_cases h : G.evaluator.extra = 0 <;> simp [destination, h]
  · rfl

private theorem source_run (final : Bool) (m : Memory G.w) :
    runSegment (Pieces.component G.components (stage final) G.g G.lit) 4 (some 0) m
      (List.replicate 1 []) = some [report G final] := by
  have h := execute_putStage (tag G final) (operands G final) 0 m [] 0
  change execute _ 4 _ m [] = some (report G final) at h
  have hc : execute (Pieces.component G.components (stage final) G.g G.lit) 4
      ((Pieces.component G.components (stage final) G.g G.lit).start 0) m [] = some (report G final) := by
    cases final <;> exact h
  simp only [List.replicate_succ, List.replicate_zero, runSegment, hc, Option.map_some]

/-- Every accepted continuation has a unique preimage after the initial or
final control write, with its complete linked report added to the cap. -/
noncomputable def handoff (final : Bool) (hclock : 51 ≤ G.clock) (m : Memory G.w)
    (ht : G.tagged (stage final) m) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 (transferred G final m)
      (fun rs => cap (G.linkedLogs (stage final) [report G final] ++ rs)) ≃
      ActualPaths G.P G.clock 0 m cap :=
  G.deterministicHandoff hclock ht (PreservesTagOnReturns.singleton_accept _ _ _ (by rfl))
    (next_stage G final) (source_run G final m) (by rfl) (by rfl) cap

theorem linked_cost (final : Bool) (hclock : 51 ≤ G.clock) (m : Memory G.w)
    (ht : G.tagged (stage final) m) :
    RAMBuckets.cost Report.probes (G.linkedLogs (stage final) [report G final]) = 4 := by
  have hc := (G.component_completion hclock ht (PreservesTagOnReturns.singleton_accept _ _ _ (by rfl))
    (source_run G final m) (by rfl)).2.2.2
  rw [hc, next_stage]; rfl

/-- After the tag transfer the final bank still stores precisely the accepting
configuration, including all zero tape cells. -/
theorem final_image {M : ℕ} (hw : 2 ≤ G.w) (hs : G.evaluator.extra+2 ≤ 2^G.w)
    (m : Memory G.w) (zero : ∀ k : Fin (fieldWords M), m ((operands G true 1).val+k.val) = 0)
    (outside : G.addr.val < (operands G true 1).val ∨ (operands G true 1).val+fieldWords M ≤ G.addr.val) :
    Stores hw hs (operands G true 1).val (transferred G true m) (.accepted : Code G.evaluator.extra M) := by
  intro k
  have h := final_stores hw hs (operands G true 1) m zero k
  change writeMemory (put G true m) G.addr _ _ = _
  have he : (operands G true 1).val + k.val ≠ G.addr.val := by have := k.isLt; omega
  rw [writeMemory, ite_eq_right he]
  exact h

end LiveProgram.EvaluatorSentinel

end VPVNP
end Computability
end OAI
