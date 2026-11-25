import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepBatches
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffective

/-! # Effective register programs for a sequence of address permutations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PermutationSweep

open IntegerMultiplication Code Space Benes EffectiveBoundedTask

variable {P : Type} [Primcodable P] {X : P → Type}

set_option maxRecDepth 4500 in
set_option maxHeartbeats 2400000 in
/-- Compile the forest sweep around the supplied program of each candidate, retaining its
native time and peak register bounds. Every directory item is read from the input. -/
theorem runFamily {Address Payload : (p : P) → X p → Type} {Stage : Type} [Inhabited Stage]
    (jobs : (p : P) → X p → List Stage) (stage : ∀ p (x : X p), Stage → Equiv.Perm (Address p x))
    (key : ∀ p, X p → Stage → Tree) (array : ∀ p (x : X p), (Address p x → Payload p x) → Tree)
    (input : ∀ p (x : X p), Address p x → Payload p x) (tick volume work : ∀ p, X p → ℕ)
    (step : Family
      (fun p (z : (x : X p) × {a // a ∈ jobs p x} × Equiv.Perm (Address p x)) => tick p z.1)
      (fun p z => work p z.1)
      (fun p z => .fork (key p z.1 z.2.1) (array p z.1 (scatter z.2.2 (input p z.1))))
      (fun p z => array p z.1 (scatter (stage p z.1 z.2.1) (scatter z.2.2 (input p z.1)))))
    (directoryFits : ∀ p x, (Task.forest (key p x) (jobs p x)).count ≤ volume p x)
    (arrayFits : ∀ p x (g : Equiv.Perm (Address p x)), (array p x (scatter g (input p x))).count ≤ volume p x) :
    Family (fun p x => (jobs p x).length * tick p x + volume p x) (fun p x => volume p x + work p x)
      (fun p x => .fork (Task.forest (key p x) (jobs p x)) (array p x (input p x)))
      (fun p x => array p x ((jobs p x).foldl (fun v s => scatter (stage p x s) v) (input p x))) := by
  apply step.sweep
  intro p c contract
  exact command_contract (RegisterTagFold.command c) from
    run (jobs p) (stage p) (key p) (array p) (input p) (tick p) (volume p) (work p)
      contract.task (directoryFits p) (arrayFits p)

section Batches

variable {E B V : (p : P) → X p → Type}
variable (w : ∀ p (x : X p), B p x → ℕ) (tables : ∀ p (x : X p), E p x → B p x → RawTable)
variable (which : ∀ p (x : X p), B p x → ℕ) (half : ∀ p, X p → Bool × ℕ)

local notation "Address" => fun p x => PackedAddress (E p x) (w p x)

set_option maxRecDepth 4500 in
set_option maxHeartbeats 2400000 in
/-- Emit the full packed half-stage from the batch command family. The emitter uses a
fixed wrapper, so the register bound is the larger of three and the child bound. -/
theorem halfStageFamily (batches : ∀ p, X p → ℕ) (belongs : ∀ p x b, which p x b < batches p x)
    (key : ∀ p, X p → ℕ → Tree) (array : ∀ p (x : X p), (Address p x → V p x) → Tree)
    (v : ∀ p (x : X p), Address p x → V p x) (tick volume work : ∀ p, X p → ℕ)
    (kernel : Family
      (fun p (z : (x : X p) × Fin (batches p x) × Equiv.Perm (Address p x)) => tick p z.1)
      (fun p z => work p z.1)
      (fun p z => .fork (key p z.1 z.2.1.val) (array p z.1 (scatter z.2.2 (v p z.1))))
      (fun p z => array p z.1 (scatter (batchStage (which p z.1) (w p z.1)
        (tables p z.1) (half p z.1) z.2.1.val) (scatter z.2.2 (v p z.1)))))
    (directoryFits : ∀ p x, (Task.forest (key p x) (List.range (batches p x))).count ≤ volume p x)
    (arrayFits : ∀ p x ψ, (array p x (scatter ψ (v p x))).count ≤ volume p x) :
    Family (fun p x => batches p x*tick p x+volume p x) (fun p x => volume p x+work p x)
      (fun p x => .fork (Task.forest (key p x) (List.range (batches p x))) (array p x (v p x)))
      (fun p x => array p x (scatter (packedStage (w p x) (tables p x) (half p x)) (v p x))) := by
  apply kernel.sweep
  intro p c contract
  exact command_contract (RegisterTagFold.command c) from
    halfStage (w p) (tables p) (which p) (half p) (batches p) (belongs p) (key p) (array p)
      (v p) (tick p) (volume p) (work p) contract.task (directoryFits p) (arrayFits p)

end Batches
end PermutationSweep

end NearSquareRoot
end Computability
end OAI
