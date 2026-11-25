import OAI.Optimization.LinearProgramming.Compression.RoundingBudgets
import OAI.Optimization.LinearProgramming.Compression.InnerWire
import OAI.Optimization.LinearProgramming.Contraction.Dyadic
import OAI.Optimization.LinearProgramming.Lattice.QueryTheorem

/-! The framed input and both genuine binary radius arguments of the numerical service
fit dimension polynomials before any matrix-dependent comparison is made. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Polynomial

noncomputable def basePolynomial : Polynomial ℕ := 10+4*X+4*(X+1)^6
noncomputable def parameterPolynomial : Polynomial ℕ := basePolynomial+
  RoundingBudgets.epochInputP.bound.comp basePolynomial+RoundingBudgets.requestInputP.bound.comp basePolynomial+16
noncomputable def countPolynomial : Polynomial ℕ := 100*X^6+1
theorem parameterSizes (N g rank : ℕ) (member : Bool) (hg : g≤paperWidth N) (hr : rank≤g) :
    let x : Input := ((N,g),member,rank)
    let B := parameterPolynomial.eval N
    (inputEncoding x).length≤B ∧ (inputCode x).length≤B ∧
      (g+1)+(epochFormBudget g (paperWidth N) (epochHeightFor N g)).size+12≤B ∧ (g+2)+((g+3)*(requestCutoff (g+1)+3)).size+12≤B := by
  intro x B
  have hb : rank.size≤rank := Nat.size_le.mpr (Nat.lt_two_pow_self (n := rank))
  have dim : (RoundingBudgets.inputsCode (N,g)).length≤basePolynomial.eval N := by
    simp [RoundingBudgets.inputsCode,prodCode,pairBits_length,unaryCode,basePolynomial,paperWidth] at hg ⊢
    omega
  have el := RoundingBudgets.epochInputP.output_length_le (N,g)
  have rl := RoundingBudgets.requestInputP.output_length_le (N,g)
  have ep : RoundingBudgets.epochInputP.bound.eval (RoundingBudgets.inputsCode (N,g)).length ≤
      RoundingBudgets.epochInputP.bound.eval (basePolynomial.eval N) := Procedure.eval_nat_mono _ dim
  have rp : RoundingBudgets.requestInputP.bound.eval (RoundingBudgets.inputsCode (N,g)).length ≤
      RoundingBudgets.requestInputP.bound.eval (basePolynomial.eval N) := Procedure.eval_nat_mono _ dim
  have el' : 2*(g+1)+1+(epochFormBudget g (paperWidth N) (epochHeightFor N g)).size ≤ (RoundingBudgets.inputsCode (N,g)).length+
      RoundingBudgets.epochInputP.bound.eval (RoundingBudgets.inputsCode (N,g)).length := by
    simpa [prodCode,pairBits_length,unaryCode,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using el
  have rl' : 2*(g+2)+1+((g+3)*(requestCutoff (g+1)+3)).size ≤ (RoundingBudgets.inputsCode (N,g)).length+
      RoundingBudgets.requestInputP.bound.eval (RoundingBudgets.inputsCode (N,g)).length := by
    simpa [prodCode,pairBits_length,unaryCode,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using rl
  have frame_length (w : Word) : (frame w).length = 2*w.length+1 := by
    rw [← quoteBits_eq_frame]
    exact quoteBits_length w
  have hw : (inputEncoding x).length≤basePolynomial.eval N := by
    simp only [x,inputEncoding,inputWord,List.length_append,List.length_cons,List.length_nil,frame_length,
      List.length_replicate,Contraction.encodeNat_length]
    simp [basePolynomial,paperWidth] at hg ⊢; omega
  have hi : (inputCode x).length≤basePolynomial.eval N := by
    simp [inputCode,x,prodCode,pairBits_length,unaryCode,boolCode,basePolynomial,paperWidth,Nat.size_eq_bits_len] at hg ⊢
    omega
  have eB : B=basePolynomial.eval N+RoundingBudgets.epochInputP.bound.eval (basePolynomial.eval N)+
      RoundingBudgets.requestInputP.bound.eval (basePolynomial.eval N)+16 := by simp [B,parameterPolynomial]
  omega

theorem parameterRoundCount (p M A : ℕ) (h : p+M.size+12≤A) : p*(2*p+1+p*searchPrecision p M)+1≤countPolynomial.eval A := by
  have hp := (rounding_parameter_bounds p M).1
  have hc : p*(2*p+1+p*searchPrecision p M)+1≤countPolynomial.eval (p+M.size+12) := by
    simpa [countPolynomial] using Nat.succ_le_succ hp
  exact hc.trans (Procedure.eval_nat_mono _ h)

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
