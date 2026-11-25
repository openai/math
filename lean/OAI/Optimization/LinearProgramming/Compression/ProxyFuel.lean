import OAI.Optimization.LinearProgramming.Compression.BitBudget
import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize

/-! A fixed cutoff exponent for the affine comparisons on minor-log proxies in §3. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Bits in an actual query row as a polynomial in the dimension and input-bound width. -/
def proxyQueryWidthFormula {R : Type*} [CommSemiring R] (p m : R) : R :=
  let u := 4*(p+1)+m+6
  let r := u*(p+1)+2
  let L := (2*p+2*r)*p+1
  u*(p+2)+1+L*(p*p+1)

/-- An upper bound on the input bit width of both invocations of sign rounding. -/
def proxyRoundingInputFormula {R : Type*} [CommSemiring R] (w B : R) : R :=
  let a := (2*w+B+14)+B+8
  let L := ((B+17)+(2+a)+1)+((B+7)+a*4)
  let n := w+1
  let u := L*(w+w+2)
  let projected := n + ((n*n+(n+u*2)*n)*2+u)
  let cuts := w+1+projected
  (w+1+cuts+1) + 4*w + 2*B + 40

/-- The exponent of the threshold `T`, calculated without inspecting the input scalars. -/
def manuscriptProxyFuelFormula {R : Type*} [CommSemiring R] (N : R) : R :=
  let w := (N+1)^6
  let B := 100*(N+1)^3
  let m := proxyRoundingInputFormula w B
  (B+7)+(w+2)+proxyQueryWidthFormula (w+2) m+(4*w+2*B+40)

/-- One fixed natural cutoff exponent for initialization and every request or restart. -/
def manuscriptProxyFuel (N : ℕ) : ℕ := manuscriptProxyFuelFormula N

noncomputable def manuscriptProxyFuelPolynomial : Polynomial ℕ := manuscriptProxyFuelFormula Polynomial.X

theorem manuscriptProxyFuelPolynomial_eval (N : ℕ) :
    manuscriptProxyFuelPolynomial.eval N = manuscriptProxyFuel N := by
  simp only [manuscriptProxyFuelPolynomial, manuscriptProxyFuel, manuscriptProxyFuelFormula,
    proxyRoundingInputFormula, proxyQueryWidthFormula, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]

theorem proxyQueryWidth_le {p w M m : ℕ} (hp : p ≤ w) (hm : M.size ≤ m) :
    Lattice.queryCoefficientWidth p M ≤ proxyQueryWidthFormula w m := by
  unfold Lattice.queryCoefficientWidth Lattice.searchPrecision Lattice.precisionExponent proxyQueryWidthFormula
  dsimp only
  gcongr

private theorem size_le_succ_of_le_two_pow {a b : ℕ} (h : a ≤ 2^b) : a.size ≤ b+1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]; have := Nat.two_pow_pos b; omega

private theorem projectionInputBits_mono {i w L : ℕ} (hi : i ≤ w) :
    fiberCommitInputBits i w L ≤ fiberCommitInputBits w w L := by
  unfold fiberCommitInputBits fiberProjectionBits projectionTestBitBound
  dsimp only
  gcongr

/-- The input coefficient cap for rounding all projected halfspaces is dominated uniformly
in the number of generators and without reference to any unobserved minor. -/
theorem manuscript_commit_inputWidth (N j : ℕ) (hj : j ≤ (N+1)^6) :
    let w := (N+1)^6
    let B := 100*(N+1)^3
    let E := 2^(B+7)
    let C := max (requestCutoff (j+1)*E) (2*E)
    let H := (B+17+4*C)*(E*C^4)
    ((j+1)*fiberProjectionBudget j w H+1).size ≤ proxyRoundingInputFormula w B := by
  intro w B E C H
  let a := fiberCoefficientBits B (2*w+B+14)
  let L := fiberClipBits B a
  have hc : C ≤ 2^a := fiberCoefficientHeight_le_two_pow B _ _ (fiber_request_height_le_two_pow hj)
  have hH : H ≤ 2^L := fiberClipHeight_le_two_pow B _ a hc
  have h := size_le_succ_of_le_two_pow (fiberCommitInput_le_two_pow j w H L hH)
  have hmono : fiberCommitInputBits j w L ≤ fiberCommitInputBits w w L :=
    projectionInputBits_mono (i := j) (w := w) (L := L) hj
  change _ ≤ fiberCommitInputBits w w L + 4*w + 2*B + 40
  omega

/-- The smaller sign-rounding bound in a requested extension is also covered, with one
extra coordinate for the newly requested minor. -/
theorem manuscript_request_inputWidth (N j : ℕ) (hj : j ≤ (N+1)^6) :
    let w := (N+1)^6
    let B := 100*(N+1)^3
    let d := j+1
    ((d+2)*(requestCutoff d+3)).size ≤ proxyRoundingInputFormula w B := by
  intro w B d
  have hK : requestCutoff d ≤ 2^(2*d+5) := by
    calc
      _ ≤ 2^(d+2)*2^(d+3) := Nat.mul_le_mul_left _ (d+3).lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hK3 : requestCutoff d+3 ≤ 2^(2*d+7) := by
    rw [show 2*d+7=2*d+5+2 by omega, pow_add]
    have hpositive : 0 < 2^(2*d+5) := Nat.two_pow_pos _
    omega
  have hM : (d+2)*(requestCutoff d+3) ≤ 2^(3*d+9) := by
    calc
      _ ≤ 2^(d+2)*2^(2*d+7) := Nat.mul_le_mul (d+2).lt_two_pow_self.le hK3
      _ = _ := by rw [← pow_add]; congr 1; omega
  have h := size_le_succ_of_le_two_pow hM
  change _ ≤ fiberCommitInputBits w w (fiberClipBits B (fiberCoefficientBits B (2*w+B+14))) +
    4*w + 2*B + 40
  dsimp only [d] at h ⊢
  change j ≤ w at hj
  omega

/-- A single exponent dominates the required LLL sign-query cutoff whenever there are at
most `w+2` homogeneous coordinates and the form bound fits the manuscript width. -/
theorem manuscript_rounding_fuel (N p M : ℕ) (hp : p ≤ (N+1)^6+2)
    (hm : M.size ≤ proxyRoundingInputFormula ((N+1)^6) (100*(N+1)^3)) :
    (100*(N+1)^3+7) + p + Lattice.queryCoefficientWidth p M ≤ manuscriptProxyFuel N := by
  have h := proxyQueryWidth_le hp hm
  unfold manuscriptProxyFuel manuscriptProxyFuelFormula
  dsimp only
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
