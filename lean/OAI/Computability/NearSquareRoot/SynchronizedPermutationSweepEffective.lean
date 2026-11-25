import OAI.Computability.NearSquareRoot.BoundedIndexedSweep
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagFold

/-! # Uniform compilation of indexed sweeps with physical workspace bounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask

open IntegerMultiplication Code CommonRegisters GeneratorSyntax Space

namespace Family

variable {P : Type} [Primcodable P] {X Y : P → Type}

/-- Wrap the emitted step in P192's table sweep. Its three register names can be
reused by the step because the run contract protects each ambient register suffix. -/
theorem sweep {a b : ∀ p, X p → ℕ} {u v : ∀ p, X p → Tree}
    {t s : ∀ p, Y p → ℕ} {input output : ∀ p, Y p → Tree}
    (step : Family a b u v)
    (run : ∀ p c, Runs c (a p) (b p) (u p) (v p) →
      Runs (RegisterTagFold.command c) (t p) (s p) (input p) (output p)) :
    Family t s input output := by
  obtain ⟨c,R,eff,_,h⟩ := step
  refine ⟨fun p => RegisterTagFold.command (c p), max 3 R, RegisterTagFold.effective eff, by omega,
    fun p => ⟨RegisterTagFold.within (le_max_left ..) _ ?_,run p _ (h p).2⟩⟩
  exact RegisterSelect.within_mono (le_max_right ..) _ (h p).1

variable (d : ∀ p, X p → ℕ) (table state : ∀ p, X p → ℕ → Tree)

/-- A family of table-dependent pass bounds. The loop uses a single common
register set for every program and every number of table records. -/
theorem indexedPasses (cost space : ∀ p, X p → ℕ → ℕ) (volume : ∀ p, X p → ℕ)
    (step : Family (fun p (z : (x : X p) × Fin (d p x)) => cost p z.1 z.2.val)
      (fun p z => space p z.1 z.2.val)
      (fun p z => .fork (table p z.1 z.2.val) (state p z.1 z.2.val))
      (fun p z => state p z.1 (z.2.val+1)))
    (hforest : ∀ p x, (Task.forest (table p x) (List.range (d p x))).count ≤ volume p x)
    (hstate : ∀ p x j, j ≤ d p x → (state p x j).count ≤ volume p x)
    (hspace : ∀ p x j, j < d p x → space p x j ≤ volume p x) :
    Family (fun p x => (∑ j ∈ Finset.range (d p x), (cost p x j + (table p x j).count + 1)) + 1)
      volume (fun p x => .fork (Task.forest (table p x) (List.range (d p x))) (state p x 0))
      (fun p x => state p x (d p x)) := by
  apply step.sweep
  intro p c contract
  exact command_contract (RegisterTagFold.command c) from
    BoundedTask.indexedPasses (d p) (table p) (state p) (cost p) (space p) (volume p)
      contract.task (hforest p) (hstate p) (hspace p)

/-- Constant-clock passes pay for the full directory only once, with workspace
bounded by the directory/state volume plus one copy of the step's scratch. -/
theorem indexedSweep (a volume work : ∀ p, X p → ℕ)
    (step : Family (fun p (z : (x : X p) × Fin (d p x)) => a p z.1)
      (fun p z => work p z.1)
      (fun p z => .fork (table p z.1 z.2.val) (state p z.1 z.2.val))
      (fun p z => state p z.1 (z.2.val+1)))
    (hforest : ∀ p x, (Task.forest (table p x) (List.range (d p x))).count ≤ volume p x)
    (hstate : ∀ p x j, j ≤ d p x → (state p x j).count ≤ volume p x) :
    Family (fun p x => d p x * a p x + volume p x) (fun p x => volume p x + work p x)
      (fun p x => .fork (Task.forest (table p x) (List.range (d p x))) (state p x 0))
      (fun p x => state p x (d p x)) := by
  apply step.sweep
  intro p c contract
  exact command_contract (RegisterTagFold.command c) from
    BoundedTask.indexedSweep (d p) (table p) (state p) (a p) (volume p) (work p)
      contract.task (hforest p) (hstate p)

end Family
end EffectiveBoundedTask

end NearSquareRoot
end Computability
end OAI
