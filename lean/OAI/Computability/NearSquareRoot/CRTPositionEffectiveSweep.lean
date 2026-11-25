import OAI.Computability.NearSquareRoot.CRTControlledDispatch
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagFold

/-! # The physical command for a variable position sweep

The command consumes each serialized stage descriptor and calls the supplied
dispatcher on that descriptor and the current array. Its syntax and register
bound are uniform in the number of stages.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication Code CommonRegisters GeneratorSyntax EffectiveTask

/-- The chronological sweep used by the physical position scheduler. -/
def sweepCmd (c : Cmd) : Cmd := RegisterTagFold.command c

theorem effective_sweepCmd {P : Type} [Primcodable P] {cs : P → Cmd} (hc : Effective ltr cs) :
    Effective ltr (sweepCmd ∘ cs) := RegisterTagFold.effective hc

theorem within_sweepCmd {R : ℕ} {c : Cmd} (hR : 3 ≤ R) (hc : Within R c) :
    Within R (sweepCmd c) := RegisterTagFold.within hR c hc

/-- The named sweep command executes the stages in order at the same charged
clock as the physical scheduler. -/
theorem physicalScheduleRuns {X A : Type*} {D : X → Type*}
    (stages : X → List A) (key : X → A → Tree) (box : (x : X) → D x → Tree)
    (run : (x : X) → A → Equiv.Perm (D x)) (charge : X → A → ℕ) (allowance : X → ℕ)
    (c : Cmd)
    (step : Runs c (fun i : (x : X) × {a // a ∈ stages x} × D x => charge i.1 i.2.1)
      (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
      (fun i => box i.1 (run i.1 i.2.1 i.2.2)))
    (bound : ∀ x, ∀ a ∈ stages x, charge x a + (key x a).count + 1 ≤ allowance x) :
    Runs (sweepCmd c) (fun i : (x : X) × D x => (stages i.1).length * allowance i.1 + 1)
      (fun i => .fork (Task.forest (key i.1) (stages i.1)) (box i.1 i.2))
      (fun i => box i.1 ((stages i.1).foldl (fun q a => run i.1 a q) i.2)) :=
  command_contract (sweepCmd c) from
    physicalSchedule stages key box run charge allowance ⟨c,step⟩ bound

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
