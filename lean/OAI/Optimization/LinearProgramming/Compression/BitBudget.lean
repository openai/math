import OAI.Optimization.LinearProgramming.Compression.CommitCap
import OAI.Optimization.LinearProgramming.Compression.ProjectionRational
import OAI.Optimization.LinearProgramming.Compression.OfflineBudget
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! ## Uniform bit bounds over every possible generator completion

The committed vector is fixed before a transcript or an auxiliary set of generators is
known. Summing the projection-test bounds over all admissible dimensions gives one
budget for every completion, with an explicit polynomial bound on its binary length.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- Cut bound valid simultaneously for every auxiliary dimension at most `width`. -/
def fiberProjectionBudget (k width H : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (width+1), projectionCoefficientBound d (clearedProjectionRowBound k d H)

theorem fiberProjectionBudget_term_le (k width H : ℕ) {d : ℕ} (hd : d ≤ width) :
    projectionCoefficientBound d (clearedProjectionRowBound k d H) ≤ fiberProjectionBudget k width H :=
  Finset.single_le_sum (f := fun d => projectionCoefficientBound d (clearedProjectionRowBound k d H))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))

/-- Exponent for the sum of projected-cut bounds over every auxiliary dimension. -/
def fiberProjectionBits (k width L : ℕ) : ℕ := width+1+projectionTestBitBound k width L

theorem fiberProjectionBudget_le_two_pow (k width H L : ℕ) (hH : H ≤ 2^L) :
    fiberProjectionBudget k width H ≤ 2^fiberProjectionBits k width L := by
  have mono {d : ℕ} (hd : d ≤ width) :
      projectionTestBitBound k d L ≤ projectionTestBitBound k width L := by
    unfold projectionTestBitBound
    dsimp only
    gcongr
  calc
    _ ≤ ∑ _d ∈ Finset.range (width+1), 2^projectionTestBitBound k width L := by
      apply Finset.sum_le_sum
      intro d hd
      exact (projection_test_height_le_pow k d H L hH).trans
        (Nat.pow_le_pow_right (by decide) (mono (Nat.le_of_lt_succ (Finset.mem_range.mp hd))))
    _ = (width+1)*2^projectionTestBitBound k width L := by simp
    _ ≤ 2^(width+1)*2^projectionTestBitBound k width L :=
      Nat.mul_le_mul_right _ (width+1).lt_two_pow_self.le
    _ = _ := (pow_add ..).symm

/-- Exponent for the complete affine sign query, including its constant term. -/
def fiberCommitInputBits (k width L : ℕ) : ℕ := k+1+fiberProjectionBits k width L+1

private theorem succ_le_next_two_pow {x e : ℕ} (hx : x ≤ 2^e) : x+1 ≤ 2^(e+1) := by
  rw [pow_succ]
  have := Nat.two_pow_pos e
  omega

theorem fiberCommitInput_le_two_pow (k width H L : ℕ) (hH : H ≤ 2^L) :
    (k+1)*fiberProjectionBudget k width H+1 ≤ 2^fiberCommitInputBits k width L := by
  apply succ_le_next_two_pow
  rw [pow_add]
  exact Nat.mul_le_mul (k+1).lt_two_pow_self.le (fiberProjectionBudget_le_two_pow k width H L hH)

/-- Substitute the projection-test size in the exponent covering both methods
of obtaining the fixed rational commitment. -/
def fiberCommitBits (k width L : ℕ) : ℕ :=
  fiberCommitCapFormula k (fiberCommitInputBits k width L)

theorem fiberCommitCap_budget_le_two_pow (k width H L : ℕ) (hH : H ≤ 2^L) :
    fiberCommitCap k ((k+1)*fiberProjectionBudget k width H+1) ≤ 2^fiberCommitBits k width L :=
  fiberCommitCap_le_two_pow _ _ _ (fiberCommitInput_le_two_pow k width H L hH)

theorem fiberCommitHeight_le_two_pow (k width H L : ℕ) (hH : H ≤ 2^L) :
    commitHeight k ((k+1)*fiberProjectionBudget k width H+1) ≤ 2^fiberCommitBits k width L :=
  (commitHeight_le_fiberCommitCap ..).trans (fiberCommitCap_budget_le_two_pow k width H L hH)

/-- Actual row height after imposing the fixed rational generator coordinates. -/
def fiberPinnedHeight (k width H : ℕ) : ℕ :=
  H + fiberCommitCap k ((k+1)*fiberProjectionBudget k width H+1) + 1

/-- Polynomial exponent for the height of the system with the commitment imposed. -/
def fiberPinnedBits (k width L : ℕ) : ℕ := L + fiberCommitBits k width L + 2

theorem fiberPinnedHeight_le_two_pow (k width H L : ℕ) (hH : H ≤ 2^L) :
    fiberPinnedHeight k width H ≤ 2^fiberPinnedBits k width L := by
  let c := fiberCommitBits k width L
  have hc := fiberCommitCap_budget_le_two_pow k width H L hH
  have hL : 2^L ≤ (2:ℕ)^(L+c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hc' : 2^c ≤ (2:ℕ)^(L+c) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsum : H+fiberCommitCap k ((k+1)*fiberProjectionBudget k width H+1) ≤ 2^(L+c+1) := by
    rw [pow_succ]
    exact (Nat.add_le_add (hH.trans hL) (hc.trans hc')).trans_eq (by omega)
  exact succ_le_next_two_pow hsum

/-- Exponent for the point found by tight rank and Cramer's rule in the pinned system. -/
def fiberPointBits (k width dim L : ℕ) : ℕ :=
  dim*dim + fiberPinnedBits k width L * (dim+2) * dim

theorem fiberPointHeight_le_two_pow (k width dim H L : ℕ) (hH : H ≤ 2^L) :
    offlinePointCap dim (fiberPinnedHeight k width H) ≤ 2^fiberPointBits k width dim L :=
  offlinePointCap_le_two_pow dim (fiberPinnedHeight_le_two_pow k width H L hH)

/-- Exponent for an affine minor value, on coefficients of height at most `2^A`. -/
def fiberValueBits (k width dim L A : ℕ) : ℕ :=
  dim+1 + ((A+1) + (fiberPointBits k width dim L + 1)) * (dim+2)

theorem fiberValueHeight_le_two_pow (k width dim H L C A : ℕ) (hH : H ≤ 2^L) (hC : C ≤ 2^A) :
    offlineValueCap dim C (offlinePointCap dim (fiberPinnedHeight k width H)) ≤
      2^fiberValueBits k width dim L A := by
  unfold offlineValueCap fiberValueBits
  rw [pow_add 2 (dim+1) _, pow_mul 2 ((A+1)+(fiberPointBits k width dim L+1)) _,
    pow_add 2 (A+1) _]
  exact Nat.mul_le_mul (dim+1).lt_two_pow_self.le
    (Nat.pow_le_pow_left (Nat.mul_le_mul (succ_le_next_two_pow hC)
      (succ_le_next_two_pow (fiberPointHeight_le_two_pow k width dim H L hH))) _)

/-- Exponent covering both the online request representations and the signed-subset
representations with grid denominator `2^(B+7)`. -/
def fiberCoefficientBits (B Xbits : ℕ) : ℕ := Xbits+B+8

theorem fiberCoefficientHeight_le_two_pow (B X Xbits : ℕ) (hX : X ≤ 2^Xbits) :
    max X (2 * 2^(B+7)) ≤ 2^fiberCoefficientBits B Xbits := by
  apply max_le
  · exact hX.trans (Nat.pow_le_pow_right (by decide) (by unfold fiberCoefficientBits; omega))
  · rw [Nat.mul_comm 2, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by unfold fiberCoefficientBits; omega)

/-- Exponent for the matrix and right-hand side after a four-term comparison is
collected, including both the endpoint and the affine constant. -/
def fiberClipBits (B A : ℕ) : ℕ := ((B+17) + (2+A) + 1) + ((B+7) + A*4)

theorem fiberClipHeight_le_two_pow (B C A : ℕ) (hC : C ≤ 2^A) :
    (B+17+4*C)*(2^(B+7)*C^4) ≤ 2^fiberClipBits B A := by
  have hB : B+17 ≤ (2:ℕ)^(B+17+(2+A)) := (B+17).lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : 4*C ≤ (2:ℕ)^(B+17+(2+A)) := by
    have h₁ : 4*C ≤ 2^(2+A) := by rw [pow_add]; exact Nat.mul_le_mul_left _ hC
    exact h₁.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsum : B+17+4*C ≤ 2^(B+17+(2+A)+1) := by
    rw [pow_succ]; exact (Nat.add_le_add hB hc).trans_eq (by omega)
  unfold fiberClipBits
  rw [pow_add 2 (B+17+(2+A)+1) _, pow_add 2 (B+7) _, pow_mul 2 A 4]
  exact Nat.mul_le_mul hsum (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hC 4))

/-- The polynomial exponent is monotone in the number of committed coordinates and
the completion dimension, so the same bound applies to every restart epoch. -/
theorem fiberValueBits_mono {k k' w w' d d' L L' A A' : ℕ} (hk : k ≤ k') (hw : w ≤ w')
    (hd : d ≤ d') (hL : L ≤ L') (hA : A ≤ A') :
    fiberValueBits k w d L A ≤ fiberValueBits k' w' d' L' A' := by
  unfold fiberValueBits fiberPointBits fiberPinnedBits fiberCommitBits fiberCommitCapFormula fiberCommitInputBits
    fiberProjectionBits projectionTestBitBound
  dsimp only
  gcongr

/-- Dimension-uniform bound for a completed epoch, with the actual clipping precision
and row height of Section 3. All dependence on the unknown magnitudes is removed. -/
theorem fiber_uniform_value_height_le_two_pow (B width X Xbits k dim : ℕ)
    (hk : k ≤ width) (hd : dim ≤ width) (hX : X ≤ 2^Xbits) :
    let E := (2:ℕ)^(B+7)
    let C := max X (2*E)
    let H := (B+17+4*C)*(E*C^4)
    let A := fiberCoefficientBits B Xbits
    offlineValueCap dim C (offlinePointCap dim (fiberPinnedHeight k width H)) ≤
      2^fiberValueBits width width width (fiberClipBits B A) A := by
  dsimp only
  have hC := fiberCoefficientHeight_le_two_pow B X Xbits hX
  exact (fiberValueHeight_le_two_pow k width dim _ _ _ _ (fiberClipHeight_le_two_pow B _ _ hC) hC).trans
    (Nat.pow_le_pow_right (by decide) (fiberValueBits_mono hk le_rfl hd le_rfl le_rfl))

/-- The representation chosen by the lattice request has height at most the cutoff
times the grid denominator. This estimate covers every size of the current list. -/
theorem fiber_request_height_le_two_pow {k width B : ℕ} (hk : k ≤ width) :
    requestCutoff (k+1) * 2^(B+7) ≤ 2^(2*width+B+14) := by
  have hx : requestCutoff (k+1) ≤ 2^((k+1+2)+(k+1+3)) := by
    unfold requestCutoff
    rw [pow_add 2 (k+1+2)]
    exact Nat.mul_le_mul_left _ (k+1+3).lt_two_pow_self.le
  calc
    _ ≤ 2^((k+1+2)+(k+1+3))*2^(B+7) := Nat.mul_le_mul_right _ hx
    _ = 2^(((k+1+2)+(k+1+3))+(B+7)) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The composition of the preceding bounds, interpreted over any commutative
semiring so that it can be used both as an actual polynomial and as a natural budget. -/
def onlineMinorBitFormula {R : Type*} [CommSemiring R] (N : R) : R :=
  let w := (N+1)^6
  let B := 100*(N+1)^3
  let a := (2*w+B+14)+B+8
  let L := ((B+17)+(2+a)+1)+((B+7)+a*4)
  let n := w+1
  let u := L*(w+w+2)
  let cuts := w+1+(n+((n*n+(n+u*2)*n)*2+u))
  let m := w+1+cuts+1
  let commitment := fiberCommitCapFormula w m
  let pinned := L+commitment+2
  let point := w*w+pinned*(w+2)*w
  w+1+((a+1)+(point+1))*(w+2)

/-- A fixed integer-coefficient polynomial bounding the binary lengths of the online
compression outputs, independently of the input scalars and of the transcript. -/
noncomputable def onlineMinorBitPolynomial : Polynomial ℕ :=
  onlineMinorBitFormula Polynomial.X

theorem onlineMinorBitPolynomial_eval (N : ℕ) :
    onlineMinorBitPolynomial.eval N = onlineMinorBitFormula N := by
  simp only [onlineMinorBitPolynomial, onlineMinorBitFormula, fiberCommitCapFormula, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X]

/-- The numerical output bound for the manuscript constants, written as a power of
two with the same polynomial exponent in every dimension and every epoch. -/
theorem fiber_manuscript_value_height (N k dim : ℕ) (hk : k ≤ (N+1)^6) (hd : dim ≤ (N+1)^6) :
    let width := (N+1)^6
    let B := 100*(N+1)^3
    let E := (2:ℕ)^(B+7)
    let C := max (requestCutoff (k+1)*E) (2*E)
    let H := (B+17+4*C)*(E*C^4)
    offlineValueCap dim C (offlinePointCap dim (fiberPinnedHeight k width H)) ≤
      2^(onlineMinorBitPolynomial.eval N) := by
  rw [onlineMinorBitPolynomial_eval]
  exact fiber_uniform_value_height_le_two_pow _ _ _ _ _ _ hk hd (fiber_request_height_le_two_pow hk)

end Compression
end LinearProgramming
end Optimization
end OAI
