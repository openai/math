import OAI.Optimization.LinearProgramming.PrimalDual.StageJoint
import OAI.Optimization.LinearProgramming.PrimalDual.FirstCertificate

/-! There is one dimension polynomial for every path through the actual two-call
suffix, for any fixed first-call workspace polynomial and second oracle budget. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open Polynomial

noncomputable def endingCost (m d B steps : Nat) : Nat :=
  stageBudget.eval (m+d+B) + (8*(jointLen m d+2*d)+12*(cutoff m d B)+4*rowCount m d+4*(d+m)+21) +
    2*steps + returnBudget.eval (m+d)+1

noncomputable def endingPolynomial (limit oracle : Polynomial Nat) : Polynomial Nat :=
  stageBudget.comp (X+limit) + 25000*(X+limit+1)^2 + 2*oracle + returnBudget + 1

theorem endingCost_le (limit oracle : Polynomial Nat) (m d B steps : Nat)
    (hB : B ≤ limit.eval (m+d)) (hk : steps ≤ oracle.eval (m+d)) :
    endingCost m d B steps ≤ (endingPolynomial limit oracle).eval (m+d) := by
  have overhead : 8*(jointLen m d+2*d)+12*(cutoff m d B)+4*rowCount m d+4*(d+m)+21 ≤
      25000*(m+d+B+1)^2 := by
    simp only [cutoff,jointBase,jointLen,origin,origLen,rowCount]; ring_nf; omega
  have hs : stageBudget.eval (m+d+B) ≤ stageBudget.eval (m+d+limit.eval (m+d)) :=
    eval_mono _ (by omega)
  have ho : 25000*(m+d+B+1)^2 ≤ 25000*(m+d+limit.eval (m+d)+1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  simp [endingPolynomial,eval_comp,endingCost]
  omega

/-- The joint system has exactly three times the combined dimension plus one rows and columns. -/
noncomputable def oraclePolynomial (C E : Nat) : Polynomial Nat := (C : Polynomial Nat)*(3*X+2)^E

theorem joint_time_eval (C E m d : Nat) :
    RAM.polyBound C E (rowCount m d+(d+m))=(oraclePolynomial C E).eval (m+d) := by
  have hr : rowCount m d+(d+m)+1=3*(m+d)+2 := by unfold rowCount; omega
  simp [oraclePolynomial,RAM.polyBound,hr]

theorem endingCost_mono_steps (m d B : Nat) {k K : Nat} (h : k ≤ K) :
    endingCost m d B k ≤ endingCost m d B K := by unfold endingCost; omega

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
