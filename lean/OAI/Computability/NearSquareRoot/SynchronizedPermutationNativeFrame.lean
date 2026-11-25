import OAI.Computability.NearSquareRoot.CRTControlledEffectiveTemplate
import OAI.Computability.NearSquareRoot.PhysicalWalshAgendaOps

/-! # One literal command for the two estimates on a native array operation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Effective.NativeFrame

open IntegerMultiplication Code EffectiveBoundedTask KernelEffectiveFamily PhysicalWalsh.AgendaOps Space

/-- The position and suffix rulers are parked while the variable rectangle command works
on the grouped records. Both cost estimates refer to this very command file. -/
def wrap (pre post : Cmd) (body : Template) : Template :=
  .next (.fixed pre) (.next (.right body) (.fixed post))

variable {I : Type} {pre post c : Cmd} (body : Template)
  {src machine arg result dst : I → Tree} {a b v t s p q : I → ℕ}

/-- Composition with arbitrary budgets gives a finite trajectory at every executable
tuple, regardless of whether the prescribed reserve pays its fast running time. -/
theorem arbitrary
    (start : EffectiveBoundedTask.Runs pre a b src (fun i => .fork (machine i) (arg i)))
    (inside : EffectiveBoundedTask.Runs (body.eval c) t s arg result)
    (finish : EffectiveBoundedTask.Runs post p q (fun i => .fork (machine i) (result i)) dst) :
    ∃ T S : I → ℕ, EffectiveBoundedTask.Runs ((wrap pre post body).eval c) T S src dst := by
  have park : EffectiveBoundedTask.Runs (rightCmd (body.eval c)) (fun i => (machine i).count+t i)
      (fun i => s i+(machine i).count) (fun i => .fork (machine i) (arg i))
      (fun i => .fork (machine i) (result i)) :=
    command_contract (rightCmd (body.eval c)) from inside.task.right machine
  exact ⟨_,_,compose start (compose park finish)⟩

/-- On a fitted reserve the same instructions have linear overhead in the actual array
volume. A separate arena permits the caller to keep a larger correct budget. -/
theorem fitted
    (start : EffectiveBoundedTask.Runs pre v v src (fun i => .fork (machine i) (arg i)))
    (inside : EffectiveBoundedTask.Runs (body.eval c) t s arg result)
    (finish : EffectiveBoundedTask.Runs post v v (fun i => .fork (machine i) (result i)) dst)
    (small : ∀ i, (machine i).count ≤ 7*v i) (space : ∀ i, v i ≤ s i) :
    EffectiveBoundedTask.Runs ((wrap pre post body).eval c) (fun i => v i+t i) s src dst := by
  have park : EffectiveBoundedTask.Runs (rightCmd (body.eval c)) (fun i => (machine i).count+t i)
      (fun i => s i+(machine i).count) (fun i => .fork (machine i) (arg i))
      (fun i => .fork (machine i) (result i)) :=
    command_contract (rightCmd (body.eval c)) from inside.task.right machine
  apply (compose start (compose park finish)).bound 10 8
  · intro i
    have h := small i
    change v i+((machine i).count+t i+v i)+1 ≤ 10*(v i+t i+1)
    omega
  · intro i
    have h := small i
    have hv := space i
    change max (v i) (max (s i+(machine i).count) (v i))+1 ≤ 8*(s i+1)
    omega

end Controlled.Effective.NativeFrame

end NearSquareRoot
end Computability
end OAI
