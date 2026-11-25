import OAI.Optimization.LinearProgramming.Lattice.BitBirdStep
import OAI.Optimization.LinearProgramming.Lattice.BitMatrixWord
import OAI.Optimization.LinearProgramming.Compression.Elimination

/-! ## Polynomial growth of the complete words traversed by the Bird determinant loop

The input and initial previous layer may have unrelated, ragged shapes. The fixed input is
read with zero padding, and every subsequent layer is materialized as a square matrix.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

private def stage (A F : IntMatrix) : ℕ → IntMatrix
  | 0 => F
  | t+1 => birdStepLists A (stage A F t)

private theorem iter_eq (A F : IntMatrix) (i : ℕ) :
    (birdUpdate^[i]) (A,F)=(A,stage A F i) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; rfl

private theorem factor_le {n w : ℕ} (h : n≤w) :
    2*(n+1)*(2^w+1) ≤ 2^(2*w+3) := by
  have p : 0 < 2^w := by positivity
  have hd : n+1≤2^(w+1) := by have := (Nat.lt_two_pow_self : w<2^w); rw [pow_succ]; omega
  have hand : 2^w+1≤2^(w+1) := by rw [pow_succ]; omega
  calc
    _ ≤ 2*(2^(w+1))*(2^(w+1)) := by gcongr
    _ = 2^(1+(w+1)+(w+1)) := by
      rw [pow_add (2 : ℕ) (1+(w+1)) (w+1),pow_add (2 : ℕ) 1 (w+1),pow_one]
    _ = _ := by congr 1; omega

private theorem stage_abs (A F : IntMatrix) (w : ℕ) (hn : A.length≤w)
    (hA : ∀ i j, (denseAt A.length A i j).natAbs≤2^w)
    (hF : ∀ i j, (denseAt A.length F i j).natAbs≤2^w) (t : ℕ) (i j : Fin A.length) :
    (denseAt A.length (stage A F t) i j).natAbs ≤ 2^(w+(2*w+3)*t) := by
  induction t generalizing i j with
  | zero => simpa [stage] using hF i j
  | succ t ih =>
    rw [stage,denseAt_birdStepLists]
    calc
      _ ≤ 2^(w+(2*w+3)*t) * (2*(A.length+1)*(2^w+1)) := by
        simpa only [BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Compression.BirdRegister.read] using
          Compression.birdRegister_natAbs_le (denseAt A.length A) (denseAt A.length (stage A F t))
            hA ih Nat.one_le_two_pow (.output (Finset.Ioi i) (Finset.Ioi i) i j)
      _ ≤ 2^(w+(2*w+3)*t) * 2^(2*w+3) := Nat.mul_le_mul_left _ (factor_le hn)
      _ = _ := by rw [←pow_add]; congr 1; ring

/-- The polynomial includes the original matrix, the integer sign and magnitude frames,
both row and matrix frames, and the outer pair frame. -/
noncomputable def birdIterationBound : Polynomial ℕ :=
  let x := Polynomial.X
  let b := x+(2*x+3)*x+1
  2*x+(x*(2*(x*(2*(b+3)+2)+1)+2)+1)+1

private theorem eval_bound (w : ℕ) : birdIterationBound.eval w =
    2*w+(w*(2*(w*(2*((w+(2*w+3)*w+1)+3)+2)+1)+2)+1)+1 := by simp [birdIterationBound]

/-- Uniform in arbitrary starting matrices and iteration counts. In particular no coherence
between the first and second matrix or between their row lengths is assumed. -/
theorem birdUpdate_word_growth (k : ℕ) (p : MatrixPair) (i : ℕ) (hi : i≤k) :
    (matrixPairCode ((birdUpdate^[i]) p)).length ≤ birdIterationBound.eval (k+(matrixPairCode p).length) := by
  rcases p with ⟨A,F⟩
  let w := k+(matrixPairCode (A,F)).length
  change _ ≤ birdIterationBound.eval w
  rw [eval_bound]
  have pair_size : (matrixPairCode (A,F)).length=2*(intMatrixCode A).length+(intMatrixCode F).length+1 := by
    simp [matrixPairCode,prodCode,pairBits_length]
  have aw : (intMatrixCode A).length≤w := by dsimp [w]; omega
  have fw : (intMatrixCode F).length≤w := by dsimp [w]; omega
  have nw : A.length≤w := (list_length_le_code intRowCode A).trans aw
  have cells (B : IntMatrix) (h : (intMatrixCode B).length≤w) (u v : Fin A.length) :
      (denseAt A.length B u v).natAbs ≤ 2^w :=
    (Nat.size_le.mp ((entryAt_size_le_matrix_word B u.val v.val).trans h)).le
  rw [iter_eq]
  cases i with
  | zero =>
    change (matrixPairCode (A,F)).length ≤ _
    dsimp [w]; omega
  | succ i =>
    have iw : i+1≤w := by dsimp [w]; omega
    have bit (a b : ℕ) (ha : a<A.length) (hb : b<A.length) :
        (birdCell A (stage A F i) a b).natAbs.size ≤ w+(2*w+3)*w+1 := by
      have bound := stage_abs A F w nw (cells A aw) (cells F fw) (i+1) ⟨a,ha⟩ ⟨b,hb⟩
      change (entryAt (squareTable A.length (birdCell A (stage A F i))) a b).natAbs ≤ _ at bound
      rw [squareTable_entryAt (birdCell A (stage A F i)) ⟨a,ha⟩ ⟨b,hb⟩] at bound
      have hsize := Nat.size_le_size bound
      rw [Nat.size_pow] at hsize
      exact hsize.trans (by gcongr)
    have q := square_word_bound A.length (w+(2*w+3)*w+1) (birdCell A (stage A F i))
      (fun a ha b hb => bit a b ha hb)
    simp only [matrixPairCode,prodCode,pairBits_length]
    change 2*(intMatrixCode A).length + (intMatrixCode (birdStepLists A (stage A F i))).length+1 ≤ _
    calc
      _ ≤ 2*w+(A.length*(2*(A.length*(2*((w+(2*w+3)*w+1)+3)+2)+1 )+2)+1)+1 := by
        exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 2 aw) q) 1
      _ ≤ _ := by gcongr

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
