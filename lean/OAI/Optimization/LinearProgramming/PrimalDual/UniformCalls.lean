import OAI.Optimization.LinearProgramming.PrimalDual.CallSites
import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsTrace

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace SubroutineCalls

open RAM CallSegments

/-- The same fixed two-hole template works for every valid guest with the
specified public numerical reserve and step-bound constants. -/
theorem uniform_template : Uniform family := by
  intro p C E bC bE solve
  let T := CallSegments.time p C E
  let U := Bridge.optimizationBitsPolynomial bC bE
  refine ⟨program p C E,originalSite p C E,jointSite p C E,T.eval 1,T.natDegree,U.eval 1,U.natDegree,
    registered p C E,?_⟩
  intro m d hm hd A b c
  let L := totalBits (lpInput A b++List.ofFn c)
  let H := decoderLimit d ((Bridge.calleeBitsPolynomial bC bE).eval L)
  have dim : d ≤ L := (Nat.le_add_left d m).trans (dimensions_le_optInputBits A b c)
  have wide : H ≤ polyBound (U.eval 1) U.natDegree L :=
    (Bridge.optimization_scalar_bound bC bE d L dim).trans (polynomial_eval_le_polyBound U L)
  obtain ⟨a,k,tr,full,joined,_,_,_,runtime,bits,tag,output⟩ := optimizer_trace_segments p C E bC bE solve hm hd A b c
  have initial : start [m,d] (lpInput A b++List.ofFn c) = stateAt tr 0 :=
    full.1.symm.trans (stateAt_fin tr (0 : Fin (k+1))).symm
  have covered := aligned full wide joined initial (by omega) (separated_itinerary p C E (width_positive solve) A b c a)
  rw [erased_itinerary] at covered
  refine ⟨a.tag,k,tr,by cases a <;> decide,full,runtime,bits,tag,output,?_,?_⟩
  · simpa only [Nat.zero_add] using covered
  · cases a <;> rfl

theorem exists_uniform_two_hole_optimizer : ∃ family : ℕ → ℕ → ℕ → Template, Uniform family := ⟨family,uniform_template⟩

/-- The call bound in Corollary 1.2. Every counted
invocation is a nonempty, protected interval in the one returned host trace. -/
theorem strong_two_calls_of_feasibility (h : StronglyPolynomialFeasibility) : StrongTwoCalls := by
  obtain ⟨p,C,E,bC,bE,solve⟩ := h
  obtain ⟨host,first,second,tC,tE,sC,sE,placed,correct⟩ := uniform_template p C E bC bE solve
  exact ⟨family,uniform_template,p,host,first,second,C,E,bC,bE,tC,tE,sC,sE,solve,placed,correct⟩

end SubroutineCalls
end PrimalDual
end LinearProgramming
end Optimization
end OAI
