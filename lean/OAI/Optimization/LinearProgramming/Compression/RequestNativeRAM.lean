import OAI.Optimization.LinearProgramming.Compression.RequestRAMPacked
import OAI.Optimization.LinearProgramming.Compression.RequestBasisSize
import OAI.Optimization.LinearProgramming.Compression.RequestQueries
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A single concrete RAM trace for the basis inspection in a native minor request,
with a dimension-only polynomial bit bound for every intermediate scalar. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestScreen

open RAM

/-- Polynomial budget for one numerator/denominator produced by sign rounding. -/
def requestRoundBitsFormula {R : Type*} [CommSemiring R] (d : R) : R :=
  let m := 3*d+10
  let p := d+1
  (m + (4*(p+1)+m+6)*(p+1) + 3)*p

/-- Each entry of the reduced graph matrix, and the squared threshold used to test
it, has numerator and denominator at most two raised to this polynomial. -/
def requestRowBitsFormula {R : Type*} [CommSemiring R] (d : R) : R :=
  let L := requestRoundBitsFormula d
  d + (L+1) + L*(d*(d+1)) + (4*d+12)

/-- The number of bits in scalar registers throughout the entire packed scan. -/
def requestScanBitsFormula {R : Type*} [CommSemiring R] (d : R) : R :=
  3 + 2*((d+2) + (2*(d+1)+3)*(requestRowBitsFormula d+1))

noncomputable def requestScanBitsPolynomial : Polynomial ℕ := requestScanBitsFormula Polynomial.X

@[simp] theorem requestScanBitsPolynomial_eval (d : ℕ) :
    requestScanBitsPolynomial.eval d = requestScanBitsFormula d := by
  simp [requestScanBitsPolynomial, requestScanBitsFormula, requestRowBitsFormula, requestRoundBitsFormula]

private theorem requestRoundingBudget_size (d : ℕ) :
    ((d+2)*(requestCutoff d+3)).size ≤ 3*d+10 := by
  have hd : d+3 ≤ 2^(d+3) := Nat.lt_two_pow_self.le
  have hK : requestCutoff d ≤ 2^(2*d+5) := by
    change 2^(d+2)*(d+3) ≤ _
    convert Nat.mul_le_mul_left (2^(d+2)) hd using 1
    rw [← pow_add]
    congr 1
    omega
  have hthree : 3 ≤ 2^(2*d+5) := by
    calc 3 ≤ 2^2 := by decide
         _ ≤ 2^(2*d+5) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk' : requestCutoff d + 3 ≤ 2^(2*d+7) := by
    rw [show 2*d+7 = (2*d+5) + 2 by omega, pow_add]; omega
  have hm : (d+2)*(requestCutoff d+3) ≤ 2^(3*d+9) := by
    calc
      _ ≤ 2^(d+2)*2^(2*d+7) := Nat.mul_le_mul (Nat.lt_two_pow_self.le) hk'
      _ = _ := by rw [← pow_add]; congr 1; omega
  simpa [Nat.size_pow] using Nat.size_le_size hm

/-- The homogeneous sign-rounding width at the request budget is bounded in
terms of the number of coefficients alone. -/
theorem requestRoundBits_width (d : ℕ) :
    affineCommitWidth d ((d+2)*(requestCutoff d+3)) ≤ requestRoundBitsFormula d := by
  have hs := requestRoundingBudget_size d
  unfold affineCommitWidth Lattice.radixWidth Lattice.precisionExponent requestRoundBitsFormula
  dsimp only
  gcongr

theorem nativeRequestRounded_polynomial_height {d : ℕ} (fuel k : ℕ) (mag : Fin d → ℚ)
    (hm : ∀ i, 0 < mag i) (j : Fin d) :
    let x := nativeRequestRounded fuel k mag j
    x.num.natAbs.size ≤ requestRoundBitsFormula d ∧ x.den.size ≤ requestRoundBitsFormula d := by
  obtain ⟨ha,hb⟩ := (nativeRequestRounded_correct fuel k mag hm).1 j
  exact ⟨ha.trans (requestRoundBits_width d), hb.trans (requestRoundBits_width d)⟩

/-- Starting with the actual rational rows returned by the native reduction, the same fixed
program for all dimensions halts with the first eligible row (or the sentinel row count).
The magnitude inputs appear nowhere in the operation or intermediate encoding bounds. -/
theorem native_packed_trace {n : ℕ} (fuel p : ℕ) (mag : Fin (n+1) → ℚ)
    (hm : ∀ j, 0 < mag j) :
    let w := nativeRequestRounded fuel p mag
    let rows := nativeGraphRowReducer n w
    let g := fun i => requestDecodeRow (rows i)
    ∃ k ≤ (n+1)*(9*(n+2)+19)+5, ∃ t : Fin (k+1) → State ℚ,
      Trace program (start (addressInput n) (scalarInput rows)) k t ∧
      (t (Fin.last k)).output = some 0 ∧ (t (Fin.last k)).index 28 =
        ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) ∧
      ∀ i, scalarBound (requestScanBitsPolynomial.eval (n+1)) (t i) := by
  let d := n+1
  let w := nativeRequestRounded fuel p mag
  let rows := nativeGraphRowReducer n w
  let g := fun i => requestDecodeRow (rows i)
  let E := requestRowBitsFormula d
  let L := requestRoundBitsFormula d
  have hE : d+(L+1)+L*(d*(d+1)) ≤ E := by dsimp [E, L, requestRowBitsFormula]; omega
  have hKpow : requestCutoff d^2 ≤ 2^E := by
    have h := requestGridArgs_bit_cap d 0
    have hle : 4*d+12 ≤ E := by dsimp [E,requestRowBitsFormula]; omega
    have hmono := Nat.pow_le_pow_right (n := 2) (by decide) hle
    simp only [pow_zero, Nat.mul_one, Nat.zero_add] at h
    omega
  have hspan := (nativeGraphRowReducer_correct.spec n w).2.2
  have he (i : Fin d) : rows i = requestGraphRat w (g i) := by
    apply requestDecodeRow_valid
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hh (i : Fin d) (j : Fin (d+1)) :
      ((requestGraphRat w (g i)) j).num.natAbs ≤ 2^E ∧ ((requestGraphRat w (g i)) j).den ≤ 2^E := by
    rw [← he]
    have h := nativeGraphRowReducer_height w (nativeRequestRounded_polynomial_height fuel p mag hm) i j
    exact ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hE), h.2.trans (Nat.pow_le_pow_right (by decide) hE)⟩
  obtain ⟨k,hk,t,htr,halt,hsel,hs⟩ := packed_trace w g hh
  refine ⟨k,hk,t,?_,halt,hsel,?_⟩
  · change Trace program (start (addressInput n) (scalarInput rows)) k t
    rwa [show rows = (fun i => requestGraphRat w (g i)) from funext he]
  · intro i
    have h := hs i
    rw [max_eq_left hKpow] at h
    simpa [E, d, requestScanBitsFormula, affineEvalBits, Nat.log2_two_pow, Nat.add_assoc] using h

end RequestScreen
end Compression
end LinearProgramming
end Optimization
end OAI
