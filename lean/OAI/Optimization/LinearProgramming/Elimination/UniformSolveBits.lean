import OAI.Optimization.LinearProgramming.Elimination.UniformSolve
import OAI.Optimization.LinearProgramming.Compression.ProjectionOutputBits

/-! Every scalar on the fixed rectangular-solver trace has polynomial binary size,
including partial Gram products, repeated determinant stages, and post-inverse products. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination
open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry Matrix
open scoped Matrix BigOperators

/-- A single fixed finite program simultaneously satisfies the dimension-only arithmetic
bound, exact canonical solution semantics, and a scalar bit bound polynomial in the length
of the input tape. The empty-equation case uses the direct two-instruction exit. -/
theorem uniformSolveProgram_stronglyPolynomial {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) :
    let input:=encodedGramInput (augmentedRows A b)
    let L:=totalBits input
    ∃k ≤ solveTime d m,∃tr : Fin (k+1)→State ℚ,
      Trace uniformSolveProgram (start [d+1,m] input) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      readSolution (packedGramLayout (d+1) m) (tr (Fin.last k)).memory=solve A b ∧
      readSolutionFromHeader d (tr (Fin.last k)).memory=solve A b ∧ ∀i,scalarBound (solveLengthBits L) (tr i) := by
  let T:=augmentedRows A b
  let v:=encodedGramInput T
  let L:=totalBits v
  have h3 : 3 ≤ solveLengthBits L := by dsimp only [solveLengthBits,solveBits];omega
  by_cases hm : m=0
  · subst m
    obtain ⟨tr,ht,hh,out,hout,hz⟩:=uniformSolveProgram_noRows A b
    exact ⟨2,by unfold solveTime;omega,tr,ht,hh,out,hout,fun i p=>by rw [hz i p];exact h3⟩
  · have hpos := Nat.pos_of_ne_zero hm
    let B:=L+3
    have hp (i : ℕ) : ratBits (v[i]?.getD 0) ≤ B := by
      cases hv : v[i]? with
      | none => change 3 ≤ L+3;omega
      | some q => exact (ratBits_le_totalBits_of_mem (List.mem_of_getElem? hv)).trans (Nat.le_add_right _ _)
    have hT (i : Fin (d+1)) (j : Fin m) : ratBits (T i j) ≤ B := by
      have e:=congrFun (congrFun (gramInputMatrix_encoded T) i) j
      rw [←e];exact hp _
    have nbits : (d+1)*m ≤ L := (length_encodedGramInput T) ▸ tape_length_le_totalBits v
    have rpos : d+1 ≤ L+1 := (Nat.le_mul_of_pos_right (d+1) hpos).trans (nbits.trans (Nat.le_succ L))
    have mpos : m ≤ L+1 := (Nat.le_mul_of_pos_left m (Nat.succ_pos d)).trans (nbits.trans (Nat.le_succ L))
    have bound : solveBits (d+1) m B ≤ solveLengthBits L := solveBits_mono rpos mpos le_rfl
    have hB : B ≤ solveBits (d+1) m B := by dsimp only [solveBits];omega
    obtain ⟨k,hk,tr,ht,hh,out,hout,hs⟩ := uniformSolveProgram_safe A b
      (fun q=>ratBits q ≤ solveBits (d+1) m B) (solveValues_rational T hT) (fun i=>(hp i).trans hB)
    exact ⟨k,hk,tr,ht,hh,out,hout,fun i p=>(hs i p).trans bound⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
