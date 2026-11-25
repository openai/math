import OAI.Optimization.LinearProgramming.Recovery.MaskedProgramCode
import Mathlib.Tactic.GCongr

/-! The ordinary support packet length and the cost of constructing its masked equation table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedDecision
open RAM RAM.Tape Geometry Polynomial

def lengthTerm : AddressTerm 2 := (.reg 0)*(.reg 1)+(.reg 1)

noncomputable def preparePolynomial : Polynomial ℕ :=
  let cells:=4*X+11+X*(4*X+5)+4*X+6
  MaskedInput.headers.budget+(7*(X^2+X)+1)+(4+(7*X+1)+4)+(X*(X*(cells+3)+5)+2)

theorem prepare_bound (h n : ℕ) : MaskedInput.programTime h n ≤ preparePolynomial.eval (h+n) := by
  simp only [preparePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_one,Polynomial.eval_ofNat]
  unfold MaskedInput.programTime MaskedInput.time MaskedInput.words uniformTableTime uniformEntryTime
  have prod : h*n ≤ (h+n)^2:=by rw [pow_two];gcongr <;> omega
  gcongr <;> omega

end MaskedDecision
end Recovery
end LinearProgramming
end Optimization
end OAI
