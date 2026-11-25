import OAI.Optimization.LinearProgramming.RAM.FrameFirstCall
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! Dimension-only polynomial bounds for establishing and invoking the first LP frame. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Polynomial

/-- Upper bound for the whole finite occupied frame after the first call. -/
noncomputable def firstWindowPolynomial (p : Program) (c e : Nat) : Polynomial Nat :=
  20*(X+1)^2 + 103 + C (addressBudget p + firstStatic p c e) + C c * (X+1)^e

theorem firstWindow_bound (p : Program) (c e m d : Nat) :
    firstLimit p c e m d ≤ (firstWindowPolynomial p c e).eval (m+d) := by
  have h : firstSource m d + optimizationLength m d ≤ 20*(m+d+1)^2+3 := by
    unfold firstSource optimizationLength primalLength
    ring_nf; omega
  simp only [firstWindowPolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_ofNat]
  apply max_le
  · unfold rawLimit polyBound; omega
  · omega

/-- One polynomial pays for header creation, input copies, frame cleaning and the
relocated instructions of the first call, at every dimension. -/
noncomputable def firstTimePolynomial (p : Program) (c e : Nat) : Polynomial Nat :=
  (HeaderPlan.budget (firstHeaders p c e)) + 400*(X+1)^2 + 12*firstWindowPolynomial p c e +
    100 + 2*C c*(X+1)^e

theorem firstTime_bound (p : Program) (c e m d k : Nat) (hk : k ≤ polyBound c e (m+d)) :
    firstCost p c e m d + 2*k ≤ (firstTimePolynomial p c e).eval (m+d) := by
  have h : 7*optimizationLength m d+8*(primalLength m d+optimizationLength m d)+4*m+4*d+26 ≤
      400*(m+d+1)^2+100 := by
    simp only [optimizationLength,primalLength]
    ring_nf; omega
  have hw := firstWindow_bound p c e m d
  simp only [firstTimePolynomial,firstCost,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_ofNat]
  unfold polyBound at hk
  rw [Nat.mul_assoc 2 c]
  omega

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
