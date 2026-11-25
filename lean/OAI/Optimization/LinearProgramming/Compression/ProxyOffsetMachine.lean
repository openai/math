import OAI.Optimization.LinearProgramming.Compression.SmallProxy

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- Terms whose grid numerator is zero can be left in the offset computation. -/
theorem clearedProxyOffset_eq_empty_of_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (hgrid : ∀ i ∈ large, grid i = 0) :
    clearedProxyOffset large D c a grid = clearedProxyOffset ∅ D c a grid := by
  simp only [clearedProxyOffset, Finset.sdiff_empty]
  congr 1
  apply Finset.sum_subset (Finset.sdiff_subset)
  intro i _ hi
  have hlarge : i ∈ large := by
    by_contra hn
    exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩)
  simp [hgrid i hlarge]

/-- On arbitrary mixtures of symbolic and gridded terms, the grid's default value
at a symbolic term is zero. The same finite dot product therefore computes the
integer constant of the mixed sign comparison. -/
theorem computedProxyOffset_eq_dot {n : ℕ} (fuel prec : ℕ) (c : ℤ) (a : Fin n → ℤ)
    (mag : Fin n → ℚ) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let grid i := (data i).getD 0
    dotProduct (smallProxyLeft D a) (smallProxyRight c grid) = (clearedProxyOffset large D c a grid : ℚ) := by
  dsimp only
  rw [smallProxyDot_value,clearedProxyOffset_eq_empty_of_zero
    (Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none) _ _ _ _]
  intro i hi
  simp [(Finset.mem_filter.mp hi).2]

/-- Both branches can compute the offset before preparing their exponent tape.
The program multiplies D by c as the first dot-product term. -/
theorem computedProxyOffsetRAM {n : ℕ} (fuel prec : ℕ) {A : ℤ} (c : ℤ)
    (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0 < mag i)
    (hform : |c| + ∑ i, |a i| ≤ A) (hcut : (2 : ℤ)^prec*A ≤ 2^fuel) :
    let data i := logProxyNumerator fuel prec (mag i)
    let large := Finset.univ.filter (fun i => data i = none)
    let D := (2 : ℕ)^(prec+2)
    let grid i := (data i).getD 0
    let left := smallProxyLeft D a
    let right := smallProxyRight c grid
    ∃ tr : Fin (9*(n+1)+3+1) → State ℚ,
      Trace affineEvalProgram (start [n+1] (0 :: 0 :: 0 :: affineInputPairs left right)) (9*(n+1)+3) tr ∧
      (tr (Fin.last _)).output = some 0 ∧
      (tr (Fin.last _)).data 0 = (clearedProxyOffset large D c a grid : ℚ) ∧
      ∀ i, scalarBound (3 + 2*((n+2)+(2*(n+1)+3)*(prec+2+fuel+1))) (tr i) := by
  let D := (2 : ℕ)^(prec+2)
  let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
  let H := (2 : ℕ)^(prec+2+fuel)
  obtain ⟨hl,hr⟩ := computedProxy_input_heights fuel prec c a mag hm hform hcut
  have hH : 1 ≤ H := one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
  have h₀ : (0 : ℚ).num.natAbs ≤ H ∧ (0 : ℚ).den ≤ H := ⟨by simp,by simpa using hH⟩
  obtain ⟨tr,ht,ho,hv,hs⟩ := affineVector_eval_trace (smallProxyLeft D a) (smallProxyRight c grid)
    0 hl hr h₀
  simp only [zero_add] at hv
  have hb : affineEvalBits (n+1) H = 3 + 2*((n+2)+(2*(n+1)+3)*(prec+2+fuel+1)) := by
    simp [affineEvalBits,H,Nat.log2_two_pow]
  exact ⟨tr,ht,ho,hv.trans (computedProxyOffset_eq_dot fuel prec c a mag),fun i => hb ▸ hs i⟩

end Compression
end LinearProgramming
end Optimization
end OAI
