import OAI.ThreeFlat.Diagonal.HistoryAssemblyDepth
import OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth
import OAI.ThreeFlat.Diagonal.PhysicalProgramLength
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Depth transport and stage counts for physical word histories -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open scoped Classical BigOperators
open private rootWithin from OAI.ThreeFlat.Diagonal.PhysicalShrinkWordDepth

variable {F Pins : Type} [Field F]

private def transportAssembly {S T : Shape} (e : S=T) (P : Plan F S) (V : Form S Pins)
    (J : P.Assembly V) : (e ▸ P : Plan F T).Assembly (e ▸ V) := by cases e; exact J

private theorem kernels_cast {S T : Shape} (e : S=T) (P : Plan F S) (V : Form S Pins)
    (J : P.Assembly V) (h : (e ▸ P : Plan F T).History)
    (bound : Plan.kernelsWithin 4 P (Run.historyOfCast e P h) J) :
    Plan.kernelsWithin 4 (e ▸ P : Plan F T) h (transportAssembly e P V J) := by
  cases e
  exact bound

private def allKernels {d l : ℕ} {A : State d l} (r : Run F A) (J : r.Assembler Pins) :=
  ∀ (L : A.Words Pins) (h : r.plan.History), Plan.kernelsWithin 4 r.plan h (J L)

private theorem all_recast {d l l' : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) (J : r.Assembler Pins) (bound : allKernels r J) :
    allKernels (Program.recast e A r) (Run.inputAssembler e A r J) := by
  cases e
  exact bound

private theorem all_step {d l D m : ℕ} {A : State d l} (R : Move F A D m)
    (next : ∀ b, Run F (R.next b)) (head : R.Assembler Pins) (tail : ∀ b, (next b).Assembler Pins)
    (root : rootWithin head) (other : ∀ b, allKernels (next b) (tail b)) :
    allKernels (.step R next) (Run.assembleStep R next head tail) := by
  intro L h
  refine ⟨root L h.1,?_⟩
  let step := head L h.1
  exact kernels_cast (R.target_eq h.1).symm (next h.1).plan step.words.ports.form
    (tail h.1 step.words) h.2 (other h.1 step.words (Run.tailHistory R next h))

private theorem stage_count_cast {S T : Shape} (e : S=T) (P : Plan F S)
    (h : (e ▸ P : Plan F T).History) :
    (e ▸ P : Plan F T).stageCount h = P.stageCount (Run.historyOfCast e P h) := by
  cases e
  rfl

private theorem stage_count_of_length {d l n : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (fixed : r.StageLength n) : r.plan.stageCount h = n := by
  induction r generalizing n with
  | done => exact fixed.symm
  | step R next ih =>
    cases n with
    | zero => exact False.elim fixed
    | succ n =>
      change 1+(_ : Plan F _).stageCount h.2 = n+1
      rw [stage_count_cast]
      have count := ih h.1 (Run.tailHistory R next h) (fixed h.1)
      change 1+(next h.1).plan.stageCount (Run.tailHistory R next h) = n+1
      omega

theorem program_stage_count {s : ℕ} (P : Program F s) (rem : ℕ) (A : State (2^s) (P.charge+rem))
    (h : (P.run rem A).plan.History) :
    (P.run rem A).plan.stageCount h = P.length :=
  stage_count_of_length _ h (P.stageLength_run rem A)


end Hierarchy.TraceDistribution.Physical

end
end OAI
