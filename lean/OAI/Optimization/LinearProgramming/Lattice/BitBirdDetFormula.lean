import OAI.Optimization.LinearProgramming.Lattice.BitBirdStep

/-! A dimension-independent determinant procedure on binary integer matrices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.Compression

private theorem neg_iterate (k : ℕ) (z : ℤ) : ((fun a : ℤ => -a)^[k]) z = (-1:ℤ)^k * z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',ih,pow_succ]; ring

private noncomputable def signPowerP : Procedure (prodCode unaryCode intCode) intCode
    (fun p : ℕ × ℤ => (-1:ℤ)^p.1*p.2) := by
  apply (intNeg.iterate Polynomial.X ?_).congrFun (fun x => neg_iterate x.1 x.2)
  intro n z i _
  rw [Polynomial.eval_X,neg_iterate]
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Int.natAbs_mul,Int.natAbs_pow]

@[simp] theorem birdUpdate_fst (p : MatrixPair) (k : ℕ) : ((birdUpdate^[k]) p).1 = p.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih

theorem denseAt_birdUpdate (A F : IntMatrix) (k : ℕ) :
    denseAt A.length ((birdUpdate^[k]) (A,F)).2 = ((birdStage (denseAt A.length A))^[k]) (denseAt A.length F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply' (f := birdStage _)]
    change denseAt A.length (birdStepLists ((birdUpdate^[k]) (A,F)).1 ((birdUpdate^[k]) (A,F)).2) = _
    rw [birdUpdate_fst,denseAt_birdStepLists,← birdStage_eq,ih]

def listDet (A : IntMatrix) : ℤ := if A.length = 0 then 1 else
  (-1:ℤ)^(A.length-1) * entryAt ((birdUpdate^[A.length-1]) (A,A)).2 0 0

theorem listDet_eq_det (A : IntMatrix) : listDet A = (denseAt A.length A).det := by
  cases h : A.length with
  | zero => simp [listDet,h]
  | succ k =>
    have he := denseAt_birdUpdate A A k
    rw [h] at he
    have hv := congrFun (congrFun he (0 : Fin (k+1))) 0
    change entryAt ((birdUpdate^[k]) (A,A)).2 0 0 = _ at hv
    simp only [listDet,h,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one]
    rw [hv]
    exact (det_from_birdStages _).symm

/-- Empty square matrices return one. All other dimensions share exactly one emitted
bit-stack program, with the loop count read from the length of the input row list. -/
noncomputable def listDetWithGrowthP (bound : Polynomial ℕ)
    (growth : ∀ n p i, i ≤ n → (matrixPairCode ((birdUpdate^[i]) p)).length ≤ bound.eval (n+(matrixPairCode p).length)) :
    Procedure intMatrixCode intCode listDet := by
  let B := identity intMatrixCode
  let n := OAI.Optimization.LinearProgramming.PriceGame.Learning.GenerationCost.lengthUnaryP intRowCode ([] : List ℤ)
  let k := unaryPred.comp n
  let run := birdUpdateP.iterate bound growth
  let table := (second intMatrixCode intMatrixCode).comp (run.comp (k.pair (B.pair B)))
  let zero := constant intMatrixCode Nat.bits 0
  let cell := matrixEntryP.comp ((zero.pair zero).pair table)
  let nonempty := signPowerP.comp (k.pair cell)
  let test := binaryZero.comp (unaryToBits.comp n)
  exact (conditional test (constant intMatrixCode intCode (1:ℤ)) nonempty).congrFun (by
    intro A; by_cases h : A.length = 0 <;> simp [listDet,h])

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
