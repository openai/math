import OAI.Optimization.LinearProgramming.Lattice.LLLNative
import OAI.Optimization.LinearProgramming.Lattice.LLLLoopNative
import OAI.Optimization.LinearProgramming.RAM.Basic

/-! The exact pass count of the executable rational-basis reduction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

/-- Run the same reduction as `reduceRational`, recording the number of size-reduction passes. -/
def reduceRationalTrace {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ) :
    Matrix (Fin (p+1)) (Fin n) ℚ × ℕ :=
  let b := HexMatrixMathlib.matrixEquiv.symm (integralRows A : Matrix (Fin (p+1)) (Fin n) ℤ)
  let run := nativeReductionTrace b (Nat.succ_pos p)
  (fun i => unscaleIntegerRow (matrixDenominator A) (HexMatrixMathlib.matrixEquiv run.1.state.b i), run.2)

/-- The costed run produces exactly the same output matrix as the native rational algorithm. -/
theorem reduceRationalTrace_result {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ) :
    (reduceRationalTrace A).1 = reduceRational A := by
  simp only [reduceRationalTrace, nativeReductionTrace_result]
  rfl

/-- Bound on the *actual* number of size-reduction passes, in terms of the original rational
matrix dimensions and the maximum length of an input numerator or denominator. -/
theorem reduceRationalTrace_count {p n L : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A) (hnum : ∀ i j, (A i j).num.natAbs ≤ 2^L)
    (hden : ∀ i j, (A i j).den ≤ 2^L) :
    let r := p+1
    let K := L + L*n*r
    (reduceRationalTrace A).2 ≤ 2 * (3*((r+n+2*K)*r*r) + 1) + r := by
  let B : Matrix (Fin (p+1)) (Fin n) ℤ := integralRows A
  let b := HexMatrixMathlib.matrixEquiv.symm B
  have he : HexMatrixMathlib.matrixEquiv b = B := HexMatrixMathlib.matrixEquiv.apply_symm_apply B
  have hi := integralRows_linearIndependent A ((euclideanRow_linearIndependent_iff A).mpr hA)
  have hib : b.independent := native_independent_of_rows b (he.symm ▸ hi)
  have hab (i : Fin (p+1)) (j : Fin n) :
      (HexMatrixMathlib.matrixEquiv b i j).natAbs ≤ 2 ^ (L + L*n*(p+1)) := by
    rw [he]
    exact integralRows_natAbs_le A hnum hden i j
  exact nativeReductionTrace_count b (Nat.succ_pos p) hib hab

/-- Fifth-degree bound in the sum of the original rational coefficient lengths alone. -/
theorem reduceRationalTrace_count_input {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (hA : LinearIndependent ℚ A) :
    (reduceRationalTrace A).2 ≤ RAM.polyBound 40 5 (∑ i, ∑ j, RAM.ratBits (A i j)) := by
  let L := ∑ i, ∑ j, RAM.ratBits (A i j)
  have row_le (i : Fin (p+1)) : (∑ j, RAM.ratBits (A i j)) ≤ L :=
    Finset.single_le_sum (f := fun s => ∑ j, RAM.ratBits (A s j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hentry (i : Fin (p+1)) (j : Fin n) : RAM.ratBits (A i j) ≤ L :=
    (Finset.single_le_sum (f := fun k => RAM.ratBits (A i k)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans (row_le i)
  have hn : n ≤ L := calc
    n = ∑ _j : Fin n, 1 := by simp
    _ ≤ ∑ j, RAM.ratBits (A 0 j) := Finset.sum_le_sum fun _ _ => by unfold RAM.ratBits; omega
    _ ≤ L := row_le 0
  have hp : p+1 ≤ n := by simpa using hA.fintype_card_le_finrank
  have hnum (i) (j) : (A i j).num.natAbs ≤ 2^L := by
    have hh := hentry i j
    unfold RAM.ratBits at hh
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega)))
  have hden (i) (j) : (A i j).den ≤ 2^L := by
    have hh := hentry i j
    unfold RAM.ratBits at hh
    exact Nat.le_of_lt (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega)))
  have hpL := hp.trans hn
  calc
    (reduceRationalTrace A).2 ≤
        2 * (3*((p+1+n+2*(L+L*n*(p+1)))*(p+1)*(p+1))+1)+(p+1) :=
      reduceRationalTrace_count A hA hnum hden
    _ ≤ 2 * (3*((L+L+2*(L+L*L*L))*L*L)+1)+L := by gcongr
    _ ≤ 40*(L+1)^5 := by ring_nf; omega

end Lattice
end LinearProgramming
end Optimization
end OAI
