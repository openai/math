import OAI.Optimization.LinearProgramming.Recovery.MaskedProgram
import OAI.Optimization.LinearProgramming.Recovery.PairWidth
import OAI.Optimization.LinearProgramming.Recovery.PairTime

/-! Closed unary polynomial bounds at the actual row-constraint memory layout of a masked LP test. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedInput
open RAM Polynomial PairBuilder

noncomputable def pairTimePolynomial : Polynomial ℕ := PairBuilder.timePolynomial.comp (256+4*X+2*X^2)
noncomputable def pairEntryPolynomial : Polynomial ℕ := PairBuilder.pairWidthPolynomial.comp (2*X)
noncomputable def pairCapacityPolynomial : Polynomial ℕ :=
  let z : Polynomial ℕ := 3*X+2
  C PairBuilder.codeReserve+6000000*z^9+z^2+2*z+4

theorem pairTime_le (h n : ℕ) : PairBuilder.time (pairLayout h n) ≤ pairTimePolynomial.eval (h+n) := by
  apply (PairBuilder.time_le_eval (pairLayout h n)).trans
  simp only [pairTimePolynomial,eval_comp]
  apply Compression.Inner.Cost.eval_nat_mono
  simp only [pairLayout,scratchBase,outputBase,flagBase,bottom,base,words,eval_add,eval_mul,eval_X,eval_pow,eval_ofNat]
  have hh : n ≤ h+n := by omega
  have hm := Nat.mul_le_mul_right (h+n) hh
  nlinarith only [hm,show 0 ≤ h by exact Nat.zero_le _]

theorem pairWidth_le (h n e : ℕ) : PairBuilder.pairWidth (h+n) n e ≤ pairEntryPolynomial.eval (h+n+e) := by
  apply (PairBuilder.pairWidth_le_eval _ _ _).trans
  simp only [pairEntryPolynomial,eval_comp,eval_mul,eval_ofNat,eval_X]
  exact Compression.Inner.Cost.eval_nat_mono _ (by omega)

theorem rowWidth_le (h n e : ℕ) : PairBuilder.rowWidth (h+n) n e ≤ pairEntryPolynomial.eval (h+n+e) :=
  (PairBuilder.firstWidth_le _ _ _).trans (pairWidth_le h n e)

theorem residualWidth_le (h n e : ℕ) : PairBuilder.residualWidth n n (PairBuilder.rowWidth (h+n) n e) ≤ pairEntryPolynomial.eval (h+n+e) :=
  (PairBuilder.residualWidth_le _ _ _).trans (pairWidth_le h n e)

theorem kernelRowWidth_le (h n e : ℕ) : PairBuilder.rowWidth n n (PairBuilder.residualWidth n n (PairBuilder.rowWidth (h+n) n e)) ≤ pairEntryPolynomial.eval (h+n+e) :=
  (PairBuilder.lastWidth_le _ _ _).trans (pairWidth_le h n e)

theorem pairCapacity_le (h n : ℕ) : PairBuilder.capacity (h+n) n 0 ≤ pairCapacityPolynomial.eval (h+n) := by
  simp only [PairBuilder.capacity,PairBuilder.workerTime,PairBuilder.scale,pairCapacityPolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat,zero_add]
  have hz : h+n+2*n+2 ≤ 3*(h+n)+2 := by omega
  gcongr
end MaskedInput
end Recovery
end LinearProgramming
end Optimization
end OAI
