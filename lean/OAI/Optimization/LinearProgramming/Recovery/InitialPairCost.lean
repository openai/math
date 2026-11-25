import OAI.Optimization.LinearProgramming.Recovery.InitialPairShared
import OAI.Optimization.LinearProgramming.Recovery.PairTime
import OAI.Optimization.LinearProgramming.Recovery.PairWidth

/-! Uniform public polynomials for both resources of the actual initial physical fragment. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM Polynomial

noncomputable def fragmentPolynomial : Polynomial ℕ :=
  let w : Polynomial ℕ := X*X+X
  let dim : Polynomial ℕ := X+1
  let room : Polynomial ℕ := 256+w+w+3*(dim*dim)
  4*stepPolynomial + PairBuilder.timePolynomial.comp (X+2+room)

noncomputable def widthPolynomial : Polynomial ℕ :=
  X + PairBuilder.pairWidthPolynomial.comp (X+2)

noncomputable def sourceWidthPolynomial : Polynomial ℕ := widthPolynomial.comp (X+3)

theorem fragmentTime_le (m d : ℕ) : fragmentTime m d ≤ fragmentPolynomial.eval (m+d) := by
  let x := m+d
  let q := x+1
  have m' : m ≤ x := by dsimp [x]; omega
  have d' : d ≤ x := by dsimp [x]; omega
  have n : m+1 ≤ q := Nat.add_le_add_right m' _
  have h : d+1 ≤ q := Nat.add_le_add_right d' _
  have w : PublicInput.words m d ≤ x*x+x := Nat.add_le_add (Nat.mul_le_mul m' d') m'
  have g : PublicInput.matrixBase m d ≤ 256+(x*x+x)+(x*x+x) := by
    unfold PublicInput.matrixBase PublicInput.sourceBase
    omega
  have a := Nat.mul_le_mul n h
  have b := Nat.mul_le_mul h n
  have c := Nat.mul_le_mul n n
  have arg : d+1+(m+1)+(layout m d).scratch+(layout m d).previous ≤
      x+2+(256+(x*x+x)+(x*x+x)+3*(q*q)) := by
    change d+1+(m+1)+(PublicInput.matrixBase m d+(m+1)*(d+1)+(d+1)*(m+1)+(m+1)*(m+1))+0 ≤ _
    have split : d+1+(m+1)=x+2 := by dsimp [x]; omega
    omega
  have tm := (PairBuilder.time_le_eval (layout m d)).trans (eval_le PairBuilder.timePolynomial arg)
  change 4*stepPolynomial.eval x + PairBuilder.time (layout m d) ≤ fragmentPolynomial.eval x
  simpa only [fragmentPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,q] using
    Nat.add_le_add_left tm (4*stepPolynomial.eval x)

theorem fragmentWidth_le (m d e : ℕ) : fragmentWidth m d e ≤ widthPolynomial.eval (m+d+e) := by
  have hb := PairBuilder.pairWidth_le_eval (d+1) (m+1) e
  rw [show d+1+(m+1)+e=m+d+e+2 by omega] at hb
  simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat]
  unfold fragmentWidth
  omega

theorem rawWidth_le {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    fragmentWidth m d (max 3 (totalBits (lpInput A b))) ≤
      sourceWidthPolynomial.eval (m+d+totalBits (lpInput A b)) := by
  rw [sourceWidthPolynomial,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  exact (fragmentWidth_le m d _).trans (eval_le widthPolynomial (by omega))

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
