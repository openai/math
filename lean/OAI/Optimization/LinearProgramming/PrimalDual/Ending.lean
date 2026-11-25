import OAI.Optimization.LinearProgramming.PrimalDual.EndingCost
import OAI.Optimization.LinearProgramming.PrimalDual.SecondRay
import OAI.Optimization.LinearProgramming.PrimalDual.SecondOptimum
import OAI.Optimization.LinearProgramming.PrimalDual.CodeLayout
import OAI.Optimization.LinearProgramming.PrimalDual.InvokeJoint

/-! The suffix of the ordinary optimization RAM links two actual isolated invocation
outcomes to the three public halts. No output values are chosen apart from the
scalars contained in the two callee traces. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Tape RAM.Block Polynomial

def endingBlocks : EndBlocks := ⟨firstCertificate,secondOptimum,secondRay,stageJoint,Call.prepareCallInputs⟩
def firstReturn := endingBlocks.firstRet
def endingCode := endingBlocks.emit

theorem afterFirst_certificate {m d H B pc : Nat} {target original : Program}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (first : State ℚ)
    (cert : Certificate A b (readVector first 0 m)) (s : Memory ℚ)
    (safe : Good (fun q => ratBits q ≤ H) s) (hm : s.index 9=m) (hd : s.index 11=d)
    (even : ∀ i, s.data (2*i)=first.data i) (placed : CodeAt target pc (endingCode original pc)) :
    ∃ n ≤ endingCost m d B 0, ∃ z, Execution target (scalarBound (decoderLimit d H))
      (s.atPC (firstReturn pc 1)) n z ∧ OptimizationOutput A b c z := by
  have parts := EndBlocks.placed (bs := endingBlocks) placed
  obtain ⟨t,k,run,hk,out⟩ := firstCertificate_correct A b c first cert s safe hm hd even
  obtain ⟨z,halt,out⟩ := decoder_exit (run.weaken (fun _ h i => (h i).trans (decoderLimit_bounds d H).1))
    parts.first out
  exact ⟨k+1,by unfold endingCost; omega,z,halt,out⟩

theorem afterFirst_feasible {m d H B pc k : Nat} {target original : Program}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀)
    (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s) (hz : 3 ≤ H)
    (hm : s.index 9=m) (hd : s.index 11=d) (hB : s.index 21=B)
    (saved : ∀ i < origLen m d, s.data (3+2*i)=optInputWord A b c i)
    (guest : ∀ i : Fin d, s.data (2*i.val)=x₀ i)
    (dataTail : ∀ i, B+2 ≤ i → s.data (2*i)=0) (indexTail : ∀ i, B+2 ≤ i → s.index (2*i)=0)
    (tr : Fin (k+1) → State ℚ)
    (oracle : Trace original (start [rowCount m d,d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))) k tr)
    (oracleSafe : ∀ i, scalarBound H (tr i))
    (answer : FeasibilityOutput (finJointMatrix A b c) (finJointRhs b c) (tr (Fin.last k)))
    (placed : CodeAt target pc (endingCode original pc)) :
    ∃ n ≤ endingCost m d B k, ∃ z, Execution target (scalarBound (decoderLimit d H))
      (s.atPC (firstReturn pc 0)) n z ∧ OptimizationOutput A b c z := by
  have parts := EndBlocks.placed (bs := endingBlocks) placed
  obtain ⟨u,j,run₀,hj,r⟩ := stageJoint_correct A b c x₀ s safe hz hm hd hB saved guest dataTail indexTail
  let last := tr (Fin.last k)
  obtain ⟨tag,done⟩ : ∃ tag, last.output=some tag := answer.elim
    (fun h => ⟨0,h.1⟩) (fun h => ⟨1,h.1⟩)
  obtain ⟨l,hl,w,call,returned⟩ := invokeJoint A b c x₀ u run₀.safe_end hz r parts.prepare parts.callee
    tr oracle oracleSafe done
  have initialRun := (run₀.compile_correct parts.stage).append call
  have large (v : State ℚ) (h : scalarBound H v) : scalarBound (decoderLimit d H) v :=
    fun i => (h i).trans (decoderLimit_bounds d H).1
  have pre := initialRun.weaken large
  have cost : j+l+(returnBudget.eval (m+d)+1) ≤ endingCost m d B k := by
    unfold endingCost; unfold secondCallCost at hl; omega
  rcases answer with ⟨h0,feas⟩ | ⟨h1,cert⟩
  · have ht : tag=0 := Option.some.inj (done.symm.trans h0)
    subst tag
    obtain ⟨t,q,decode,hq,out⟩ := secondOptimum_correct A b c last feas w call.safe_end
      returned.rows returned.cols (fun i _ => returned.guest i) returned.objective
    have hq' : q ≤ returnBudget.eval (m+d) := by simpa [returnBudget] using hq
    obtain ⟨z,halt,out⟩ := decoder_exit decode parts.optimum out
    exact ⟨j+l+(q+1),by omega,z,pre.append halt,out⟩
  · have ht : tag=1 := Option.some.inj (done.symm.trans h1)
    subst tag
    obtain ⟨t,q,decode,hq,out⟩ := secondRay_correct A b c x₀ hx₀ last cert w call.safe_end
      returned.rows returned.cols returned.guest returned.objective returned.point
    obtain ⟨z,halt,out⟩ := decoder_exit decode parts.ray out
    exact ⟨j+l+(q+1),by omega,z,pre.append halt,out⟩

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
