import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Framing specified commands for a Walsh agenda -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.AgendaOps

open IntegerMultiplication Code Space EffectiveBoundedTask

variable {I : Type} {c d : Cmd} {t s t' s' : I → ℕ} {u v w : I → Tree}

theorem compose (h : EffectiveBoundedTask.Runs c t s u v) (g : EffectiveBoundedTask.Runs d t' s' v w) :
    EffectiveBoundedTask.Runs (c.join d) (fun i => t i+t' i) (fun i => max (s i) (s' i)) u w :=
  command_contract (c.join d) from h.task.compose g.task

theorem left (h : EffectiveBoundedTask.Runs c t s u v) (park : I → Tree) :
    EffectiveBoundedTask.Runs (KernelEffectiveFamily.leftCmd c) t (fun i => s i+(park i).count)
      (fun i => .fork (u i) (park i)) (fun i => .fork (v i) (park i)) :=
  command_contract (KernelEffectiveFamily.leftCmd c) from h.task.left park

theorem conform {t' s' : I → ℕ} {u' v' : I → Tree} (h : EffectiveBoundedTask.Runs c t s u v)
    (ht : ∀ i, t i = t' i) (hs : ∀ i, s i = s' i)
    (hu : ∀ i, u i = u' i) (hv : ∀ i, v i = v' i) :
    EffectiveBoundedTask.Runs c t' s' u' v' := by
  simpa only [funext ht,funext hs,funext hu,funext hv] using h

theorem easy {X Y : Type} [Codec X] [Codec Y] {f : X→Y} (h : Easy f) (x : I → X) :
    EffectiveBoundedTask.Runs h.choose (fun i => size (x i)) (fun i => size (x i)+size (x i))
      (fun i => send (x i)) (fun i => send (f (x i))) := by
  apply EffectiveBoundedTask.Runs.of_time
  obtain ⟨C,hc⟩ := h.choose_spec
  exact ⟨C,fun i => hc (x i)⟩

end PhysicalWalsh.AgendaOps

end NearSquareRoot
end Computability
end OAI
