import OAI.Optimization.LinearProgramming.RAM.CallableTwoHeader
import OAI.Optimization.LinearProgramming.RAM.CallableBoot
import Mathlib.Tactic.IntervalCases

/-! An ordinary two-dimension header and contiguous scalar tape are passed to the
native finite-bank bootstrap with an input-dimension polynomial number of instructions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block Tape Call Polynomial

def twoDimBoot (len floor : AddressTerm 2) : Block := .seq (twoDimHeader len floor) bootBlock

noncomputable def twoDimCapPolynomial (len floor : AddressTerm 2) : Polynomial ℕ :=
  floor.boundValue+2*len.boundValue+72+C (twoDimStatic len floor)

noncomputable def twoDimBootPolynomial (len floor : AddressTerm 2) : Polynomial ℕ :=
  HeaderPlan.budget (twoDimPlan len floor)+4+1000*(twoDimCapPolynomial len floor+X+len.boundValue+1)^2

private theorem dim_le (m d : ℕ) (i : Fin 2) : dimensions m d i≤ m+d := by
  unfold dimensions
  split <;> omega

theorem twoDimCapPolynomial_spec (len floor : AddressTerm 2) (m d : ℕ) :
    twoDimCap len floor m d≤(twoDimCapPolynomial len floor).eval (m+d) := by
  have hl := len.value_le (dimensions m d) (m+d) (dim_le m d)
  have hf := floor.value_le (dimensions m d) (m+d) (dim_le m d)
  simp only [twoDimCap,twoDimRawCap,twoDimCapPolynomial,eval_add,eval_mul,eval_ofNat,eval_C]
  apply max_le <;> omega

/-- A single fixed RAM block takes ordinary dimensions and dense scalar words. The
block derives the cap and the scalar-tape length from the two dimensions. -/
theorem twoDimBoot_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (len floor : AddressTerm 2) (P : K → Prop) (m d : ℕ) (xs : List K)
    (hlength : xs.length=len.value (dimensions m d)) (hs : ((start [m,d] xs).memory).AllData P) (hz : P 0) :
    ∃ k≤(twoDimBootPolynomial len floor).eval (m+d), Block.Eval (Memory.AllData P)
      (twoDimBoot len floor) (start [m,d] xs).memory k
      (start (Odd.finiteDims (twoDimCap len floor m d) [] [m,d]) (Odd.finiteScalars [] xs)).memory := by
  let cap := twoDimCap len floor m d
  obtain ⟨u,k,head,hk,ptr⟩ := twoDimHeader_correct len floor m d xs hs
  obtain ⟨_,room,h64⟩ := twoDimCap_bounds len floor m d
  have hmin : minimumCap [m,d].length xs.length≤cap := by
    change minimumCap [m,d].length xs.length ≤ twoDimCap len floor m d
    simp only [minimumCap,List.length_cons,List.length_nil,hlength,max_le_iff]
    exact ⟨h64,by omega,room⟩
  have inputs (i : ℕ) (hi : i<[m,d].length) : u.index (3+i)=[m,d][i]?.getD 0 := by
    have bound : i<2 := hi
    interval_cases i
    · exact ptr.rowAt
    · exact ptr.columnAt
  have hlen : u.index 2=xs.length := ptr.lengthAt.trans hlength.symm
  obtain ⟨l,hl,boot⟩ := bootBlock_from_memory P u [m,d] xs cap hmin head.safe_end hz ptr.capAt
    ptr.countAt hlen inputs (fun j => congrFun ptr.scalar j) ptr.tail
  have cv := twoDimCapPolynomial_spec len floor m d
  have lv := len.value_le (dimensions m d) (m+d) (dim_le m d)
  have room' : cap+[m,d].sum+xs.length+1 ≤ (twoDimCapPolynomial len floor).eval (m+d)+(m+d)+len.boundValue.eval (m+d)+1 := by
    simp only [List.sum_cons,List.sum_nil,Nat.add_zero,hlength]
    dsimp only [cap]
    omega
  refine ⟨k+l,?_,head.seq boot⟩
  simp only [twoDimBootPolynomial,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one]
  exact Nat.add_le_add hk (hl.trans (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left room' 2)))

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
