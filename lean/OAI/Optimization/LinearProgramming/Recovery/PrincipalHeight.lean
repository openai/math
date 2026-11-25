import OAI.Optimization.LinearProgramming.Recovery.PrincipalTime
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientationSize
import OAI.Optimization.LinearProgramming.PrimalDual.Layout

/-! Use one rational width for each of the three global stages. Every iteration of
the support scan uses the same bound, since each of its independent numerical calls
reads the selected input basis and a 0/1 flag vector. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM Polynomial

noncomputable def seedPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ := 3+InitialPair.sourceWidthPolynomial+InitialOrientation.width s
noncomputable def vectorPolynomial (s : NormalSubspace.Spec) : Polynomial ℕ := seedPolynomial s+
  (MaskedDecision.heightPolynomial s).comp (2*(X+1)+seedPolynomial s)+WitnessProgram.heightPolynomial.comp (2*(X+1)+seedPolynomial s)
noncomputable def workerHeight (s : NormalSubspace.Spec) : Polynomial ℕ :=
  let B:=vectorPolynomial s
  let F:=3+4*B
  B+F+1_000_000*((X+1)*X*F+1)^6

private theorem seed_eq (s : NormalSubspace.Spec) (t : ℕ) :
    (seedPolynomial s).eval t=3+InitialPair.sourceWidthPolynomial.eval t+(InitialOrientation.width s).eval t:=by simp [seedPolynomial]

theorem seed_bounds (s : NormalSubspace.Spec) (x : ℕ) : 3 ≤ (seedPolynomial s).eval x ∧
    InitialPair.sourceWidthPolynomial.eval x ≤ (seedPolynomial s).eval x ∧
    (InitialOrientation.width s).eval x ≤ (seedPolynomial s).eval x := by rw [seed_eq];omega

theorem scan_height_le (s : NormalSubspace.Spec) (m d h L : ℕ) (thin : h ≤ m+1) :
    scanWidth s h (m+1) ((seedPolynomial s).eval (m+d+L)) ≤ (vectorPolynomial s).eval (m+d+L) := by
  let seed:=(seedPolynomial s).eval (m+d+L)
  have keys : h+(m+1)+seed ≤ 2*((m+d+L)+1)+seed:=by omega
  have mask:=MaskedDecision.eval_mono (MaskedDecision.heightPolynomial s) keys
  have solved:=MaskedDecision.eval_mono WitnessProgram.heightPolynomial keys
  unfold scanWidth vectorPolynomial
  simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  change max seed (max _ _) ≤ seed+_+_
  have join (a b u v : ℕ) (ha : a ≤ u) (hb : b ≤ v) : max seed (max a b) ≤ seed+u+v := by omega
  exact join _ _ _ _ mask solved

theorem finish_height_le (s : NormalSubspace.Spec) (m d h L : ℕ) (thin : h ≤ m+1) :
    PrimalOutput.outputWidth m d (scanWidth s h (m+1) ((seedPolynomial s).eval (m+d+L))) ≤ (workerHeight s).eval (m+d+L) := by
  have base:=scan_height_le s m d h L thin
  unfold workerHeight PrimalOutput.outputWidth PrimalDual.differenceWidth WitnessSolve.solverHeight
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  gcongr <;>omega

private theorem length_le_bits (xs : List ℚ) : xs.length ≤ totalBits xs:=by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    change xs.length+1 ≤ ratBits a+totalBits xs
    have one : 1 ≤ ratBits a:=by unfold ratBits;omega
    omega

/-- In the frozen theorem the scalar bound is a polynomial in the input encoding
alone. Positive m,d ensure even the matrix dimensions fit within that input size. -/
theorem dimensions_le_bits {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (hm : 0 < m) :
    m+d ≤ totalBits (lpInput A b) := by
  have length:=length_le_bits (lpInput A b)
  rw [PrimalDual.lpInput_length] at length
  have times : d ≤ m*d := (Nat.one_mul d).symm.le.trans (Nat.mul_le_mul_right d hm)
  omega

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
