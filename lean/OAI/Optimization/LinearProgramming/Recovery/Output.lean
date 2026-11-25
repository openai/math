import OAI.Optimization.LinearProgramming.Specification
import OAI.Optimization.LinearProgramming.RAM.Code

/-! Decode the outer physical branch, reading the advertised vector from the
public scalar tape. The sparse multiplier additionally carries its normalization. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal

open RAM Matrix
open scoped Matrix

def outputGuard : Cond:=.addrLT 17 16

inductive Published {K : Type*} [Field K] [LinearOrder K] {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (z : Memory K) : Prop
  | feasible (x : Fin d→K) (hx : Feasible A b x) (data : ∀j : Fin d,z.data j.val=x j) (tag : z.index 16=0) (nil : z.index 17=0)
  | infeasible (y : Fin m→K) (hy : Certificate A b y) (normalized : b ⬝ᵥ y=-1) (data : ∀j : Fin m,z.data j.val=y j) (tag : z.index 16=1) (nil : z.index 17=0)

theorem Published.decoded {K : Type*} [Field K] [LinearOrder K] {m d : ℕ} {A : Matrix (Fin m) (Fin d) K}
    {b : Fin m→K} {z : Memory K} {last : State K} (done : Published A b z) (data : last.data=z.data)
    (halt : last.output=some (if outputGuard.test z then 1 else 0)) :
    NormalizedFeasibilityOutput A b last ∧ FeasibilityOutput A b last := by
  cases done with
  | feasible x hx cells tag nil =>
    have read : readVector last 0 d=x:=funext fun j=>by simpa [readVector,data] using cells j
    have yes : last.output=some 0:=by simpa [outputGuard,Cond.test,tag,nil] using halt
    have valid : Feasible A b (readVector last 0 d):=by rwa [read]
    exact ⟨Or.inl ⟨yes,valid⟩,Or.inl ⟨yes,valid⟩⟩
  | infeasible y hy normalized cells tag nil =>
    have read : readVector last 0 m=y:=funext fun j=>by simpa [readVector,data] using cells j
    have no : last.output=some 1:=by simpa [outputGuard,Cond.test,tag,nil] using halt
    rw [←read] at hy normalized
    exact ⟨Or.inr ⟨no,hy,normalized⟩,Or.inr ⟨no,hy⟩⟩

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
