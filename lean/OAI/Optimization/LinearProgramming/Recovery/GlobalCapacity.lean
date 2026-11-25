import OAI.Optimization.LinearProgramming.Recovery.BundleSelect
import OAI.Optimization.LinearProgramming.Recovery.SupportBundle
import OAI.Optimization.LinearProgramming.Recovery.WitnessCallCode
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! One dimension-only reset capacity for all support queries, the final normalized
solve, and the actual primal input. Reentrant calls never depend on a previous rational
coefficient's representation to determine the size of this window. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal

open RAM RAM.Callable Geometry Polynomial

noncomputable def capacityPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ :=
  C (addressBudget s.program+addressBudget (MaskedDecision.program s)+addressBudget WitnessProgram.program+8)+
    (2*X+2)^2+s.clock+(MaskedDecision.clockPolynomial s).comp (2*X)+WitnessProgram.clockPolynomial.comp (2*X)

noncomputable def capacityC (s : NormalSubspace.Spec) := (capacityPolynomial s).eval 1
noncomputable def capacityE (s : NormalSubspace.Spec) := (capacityPolynomial s).natDegree
noncomputable def capacity (s : NormalSubspace.Spec) (m d : ℕ) := SupportBundle.capacity (capacityC s) (capacityE s) m d

private theorem lower (s : NormalSubspace.Spec) (m d : ℕ) : let u:=m+d+1
    addressBudget s.program+addressBudget (MaskedDecision.program s)+addressBudget WitnessProgram.program+8+
      (2*u+2)^2+s.clock.eval u+(MaskedDecision.clockPolynomial s).eval (2*u)+WitnessProgram.clockPolynomial.eval (2*u)
      < capacity s m d := by
  dsimp only
  calc
    _ = (capacityPolynomial s).eval (m+d+1) := by
      simp only [capacityPolynomial, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, eval_comp]
    _ ≤ polyBound ((capacityPolynomial s).eval 1) (capacityPolynomial s).natDegree (m+d+1) := polynomial_eval_le_polyBound _ _
    _ < capacity s m d := by unfold capacity SupportBundle.capacity capacityC capacityE;omega

theorem capacity_inputs (s : NormalSubspace.Spec) (m d h : ℕ) (hn : h ≤ m+1) :
    h*(m+1)+(m+1) ≤ capacity s m d ∧ 2 ≤ capacity s m d ∧ (d+1)*m ≤ capacity s m d := by
  let u:=m+d+1
  have a : h*(m+1) ≤ u^2:=by rw [pow_two];gcongr <;> dsimp [u] <;> omega
  have b : (d+1)*m ≤ u^2:=by rw [pow_two];gcongr <;> dsimp [u] <;> omega
  have big : u^2+2*u+4 ≤ (2*u+2)^2:=by nlinarith only [Nat.zero_le u,Nat.zero_le (u^2)]
  have bound:=lower s m d
  change _+(2*u+2)^2+_+_+_ < capacity s m d at bound
  have nle : m+1 ≤ u:=by dsimp [u];omega
  omega

theorem capacity_after_scan (s : NormalSubspace.Spec) (m d h : ℕ) (hn : h ≤ m+1) :
    SupportBundle.footprint s h (m+1) < capacity s m d ∧ WitnessCall.numericalFootprint h (m+1) < capacity s m d := by
  let u:=m+d+1
  have input : h*(m+1)+(m+1) ≤ (2*u+2)^2 := by
    have mult : h*(m+1) ≤ u^2:=by rw [pow_two];gcongr <;> dsimp [u] <;> omega
    have nle : m+1 ≤ u:=by dsimp [u];omega
    nlinarith only [mult,nle,Nat.zero_le u,Nat.zero_le (u^2)]
  have shape : h+(m+1) ≤ 2*u:=by dsimp [u];omega
  have two : 2 ≤ (2*u+2)^2:=by nlinarith only [Nat.zero_le u,Nat.zero_le (u^2)]
  have twice : 2*u ≤ (2*u+2)^2:=by nlinarith only [Nat.zero_le u,Nat.zero_le (u^2)]
  have mask:=MaskedDecision.eval_mono (MaskedDecision.clockPolynomial s) shape
  have witness:=MaskedDecision.eval_mono WitnessProgram.clockPolynomial shape
  have bound:=lower s m d
  unfold SupportBundle.footprint WitnessCall.numericalFootprint
  change _+(2*u+2)^2+_+_+_ < capacity s m d at bound
  dsimp only [u] at *
  omega

theorem capacity_after_initial {K : Type*} (s : NormalSubspace.Spec) (m d r f : ℕ) (data : List K)
    (sum : r+f=m+1) (length : data.length=(m+1)^2) :
    nativeWindow s.program [r,f] data+s.clock.eval (m+1) < capacity s m d := by
  let u:=m+d+1
  have nle : m+1 ≤ u:=by dsimp [u];omega
  have num : (m+1)^2 ≤ (2*u+2)^2:=by gcongr <;>omega
  have small : m+1 ≤ (2*u+2)^2:=by nlinarith only [nle,Nat.zero_le u,Nat.zero_le (u^2)]
  have two : 2 ≤ (2*u+2)^2:=by nlinarith only [Nat.zero_le u,Nat.zero_le (u^2)]
  have clock:=MaskedDecision.eval_mono s.clock nle
  have bound:=lower s m d
  change _+(2*u+2)^2+_+_+_ < capacity s m d at bound
  simp only [nativeWindow,length,List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,Nat.add_zero,sum]
  dsimp only [u] at *
  omega

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
