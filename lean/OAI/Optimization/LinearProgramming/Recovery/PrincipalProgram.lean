import OAI.Optimization.LinearProgramming.Recovery.PrincipalRuntime
import OAI.Optimization.LinearProgramming.RAM.CallablePublicDecision

/-! A uniform feasibility program on ordinary `[m,d]` and the original unmodified
row-major rational data, with its bounded complete trace and normalized sparse output. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM RAM.Callable Geometry Polynomial

noncomputable def program (s : NormalSubspace.Spec) : Program := Boot.publicLPDecision (fragment s) outputGuard 1 0 ((workerClock s).eval 1) (workerClock s).natDegree
noncomputable def publicClock (s : NormalSubspace.Spec) := Boot.publicLPDecisionTime (fragment s) outputGuard ((workerClock s).eval 1) (workerClock s).natDegree
noncomputable def publicHeight (s : NormalSubspace.Spec) : Polynomial ℕ := (workerHeight s).comp (2*X)

theorem program_run {m d : ℕ} (s : NormalSubspace.Spec) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (hm : 0 < m) (hd : 0 < d) :
    ∃ k≤(publicClock s).eval (m+d), ∃ tr : Fin (k+1)→State ℚ,
      Trace (program s) (start [m,d] (lpInput A b)) k tr ∧
      (∀i,scalarBound ((publicHeight s).eval (totalBits (lpInput A b))) (tr i)) ∧
      NormalizedFeasibilityOutput A b (tr (Fin.last k)) ∧ FeasibilityOutput A b (tr (Fin.last k)) := by
  let xs:=lpInput A b
  let L:=totalBits xs
  let P:=fun q=>ratBits q ≤ (workerHeight s).eval (m+d+L)
  obtain ⟨out,run,done⟩:=fragment_run s A b hm hd
  have startSafe : ((start [m,d] xs).memory).AllData P:=fun j=>by simpa only [Odd.data_slot] using run.safe_start (Odd.slot j)
  have nativeZero : P 0:=by
    have a:=run.safe_start (2*0)
    rw [Odd.data_even] at a
    exact a
  have clock:=polynomial_eval_le_polyBound (workerClock s) (m+d)
  obtain ⟨k,hk,tr,steps,branch,words,bits⟩:=Boot.publicLPDecision_correct (fragment s) outputGuard 1 0
    ((workerClock s).eval 1) (workerClock s).natDegree m d xs P out (PrimalDual.lpInput_length A b) startSafe nativeZero (run.mono clock)
  have dims : m+d≤L:=dimensions_le_bits A b hm
  have height : (workerHeight s).eval (m+d+L) ≤ (publicHeight s).eval L:=by
    simp only [publicHeight,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    exact MaskedDecision.eval_mono _ (by omega)
  obtain ⟨normalized,valid⟩:=done.decoded words branch
  exact ⟨k,hk,tr,steps,fun i j=>(bits i j).trans height,normalized,valid⟩

theorem feasibility_of_subspace (s : NormalSubspace.Spec) : StronglyPolynomialFeasibility := by
  refine ⟨program s,(publicClock s).eval 1,(publicClock s).natDegree,(publicHeight s).eval 1,(publicHeight s).natDegree,?_⟩
  intro m d hm hd A b
  obtain ⟨k,clock,tr,run,bits,_,correct⟩:=program_run s A b hm hd
  have time:=polynomial_eval_le_polyBound (publicClock s) (m+d)
  have height:=polynomial_eval_le_polyBound (publicHeight s) (totalBits (lpInput A b))
  exact ⟨k,tr,run,clock.trans time,fun i j=>(bits i j).trans height,correct⟩

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
