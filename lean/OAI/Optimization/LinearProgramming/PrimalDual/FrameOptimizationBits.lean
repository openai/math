import OAI.Optimization.LinearProgramming.PrimalDual.DecoderMath
import OAI.Optimization.LinearProgramming.PrimalDual.InputSize
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! One polynomial in the original data bounds every scalar of the two calls and their decoders. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM Polynomial

noncomputable def denseInputPolynomial : Polynomial Nat := (2*X+1)*(X+1)*(X+3)

noncomputable def calleeBitsPolynomial (bC bE : Nat) : Polynomial Nat :=
  X+3+C bC*(denseInputPolynomial+1)^bE

noncomputable def optimizationBitsPolynomial (bC bE : Nat) : Polynomial Nat :=
  let h := calleeBitsPolynomial bC bE
  let diff := 3+4*h
  8*(3+2*X*(h+diff+1)+diff+h+1)+10

/-- The same physical register invariant holds before and during either feasibility call. -/
theorem callee_bits {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (bC bE : Nat) :
    let input := lpInput A b ++ List.ofFn c
    let L := totalBits input
    let h := (calleeBitsPolynomial bC bE).eval L
    3 ≤ h ∧ L ≤ h ∧ scalarBound h (start [m,d] input) ∧
      polyBound bC bE (totalBits (lpInput A b)) ≤ h ∧
      polyBound bC bE (totalBits (lpInput (finJointMatrix A b c) (finJointRhs b c))) ≤ h := by
  let input := lpInput A b ++ List.ofFn c
  let L := totalBits input
  let T := (2*L+1)*(L+1)*(L+3)
  let H := (calleeBitsPolynomial bC bE).eval L
  have defH : H = L+3+bC*(T+1)^bE := by simp [H,calleeBitsPolynomial,denseInputPolynomial,T]
  have small : totalBits (lpInput A b) ≤ L := by simp [L,input,totalBits,List.map_append]
  have big : L ≤ T := by dsimp [T]; ring_nf; omega
  have joint := jointInput_totalBits A b c
  change totalBits (lpInput (finJointMatrix A b c) (finJointRhs b c)) ≤ T at joint
  have mono (q : Nat) (hq : q ≤ T) : polyBound bC bE q ≤ H := by
    have sm := Nat.mul_le_mul_left bC (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) bE)
    unfold polyBound; omega
  have word (j : Nat) : ratBits ((start [m,d] input).data j) ≤ H := by
    change ratBits ((input[j]?).getD 0) ≤ H
    cases hj : input[j]? with
    | none => change 3 ≤ H; omega
    | some v =>
      have hv : ratBits v ≤ L := ratBits_le_totalBits_of_mem (List.mem_of_getElem? hj)
      exact hv.trans (by omega)
  have h3 : 3 ≤ H := by omega
  have hL : L ≤ H := by omega
  exact ⟨h3,hL,word,mono _ (small.trans big),mono _ joint⟩

theorem optimization_scalar_bound (bC bE d L : Nat) (hd : d ≤ L) :
    decoderLimit d ((calleeBitsPolynomial bC bE).eval L) ≤ (optimizationBitsPolynomial bC bE).eval L := by
  simp only [optimizationBitsPolynomial,decoderLimit,dotWidth,differenceWidth,
    eval_add,eval_mul,eval_X,eval_one,eval_ofNat]
  gcongr

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
