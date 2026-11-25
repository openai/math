import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramBodyCode
import OAI.Optimization.LinearProgramming.Recovery.MaskedPreparationCost
import OAI.Optimization.LinearProgramming.RAM.CallablePublicDecision

/-! The ordinary finite RAM and its dimension-only public clock, shared by all scalar fields. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

open RAM RAM.Callable Polynomial

noncomputable def bodyPolynomial : Polynomial ℕ :=
  4*MaskedDecision.preparePolynomial +
    (4*WitnessTable.clockPolynomial + (WitnessSolve.normalizedCallPolynomial+(21*X+18)+(13*X+14)))

theorem bodyTime_bound (h n : ℕ) : bodyTime h n ≤ bodyPolynomial.eval (h+n) := by
  have masked := MaskedDecision.prepare_bound h n
  have solve := WitnessSolve.normalized_call_bound h n
  simp only [bodyPolynomial,eval_add,eval_mul,eval_X,eval_ofNat]
  unfold bodyTime WitnessSolve.time WitnessExport.time WitnessTable.capacity WitnessTable.words Publish.oddTime
  omega

/-- Both exits return tag zero. The body has already published all vector coordinates. -/
noncomputable def program : Program :=
  Boot.publicDecision MaskedDecision.lengthTerm body (.addrLT 0 0) 0 0 (bodyPolynomial.eval 1) bodyPolynomial.natDegree

noncomputable def clockPolynomial : Polynomial ℕ :=
  Boot.publicDecisionTime MaskedDecision.lengthTerm body (.addrLT 0 0) (bodyPolynomial.eval 1) bodyPolynomial.natDegree

noncomputable abbrev heightPolynomial : Polynomial ℕ := WitnessSolve.heightPolynomial

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
