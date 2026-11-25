import OAI.Optimization.LinearProgramming.NormalSubspace.Joined
import OAI.Optimization.LinearProgramming.Geometry.BorderFixedService
import OAI.Optimization.LinearProgramming.NormalSubspace.Spec
import OAI.Optimization.LinearProgramming.PrimalDual.InputSize

/-! The two uniform primitive algorithms yield a fixed marked-subspace program
on the ordinary scalar encoding. The instruction clock is independent of the
entries of both matrices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM OracleSpec Matrix Geometry Geometry.BorderBatch Recovery.PackedPCG Recovery.OracleInline Polynomial
open scoped Matrix

private theorem matrixEntry_mem {r n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (i : Fin r) (j : Fin n) :
    D i j∈MinorLog.entries D := by
  apply List.mem_flatten.mpr
  exact ⟨List.ofFn (D i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

/-- Build the ordinary rational machine from fixed programs, an arbitrary
certified clock and the restart coefficient in the public service guarantee. -/
noncomputable def fixedRationalSpecWithRestarts (init serve : Program) (p : BitProgram)
    (B T work : Polynomial ℕ) (Cr : ℕ)
    (duration : ∀ n, (joinedTime p B T Cr).eval n ≤ work.eval n)
    (services : ∀ r s (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ),
      FixedServiceAt init serve B Cr D E)
    (learner : ∀ n (i : Fin n) (f : Transcript → Word → Bool), p.ComputesWithin (fun h w => [f h w])
      (priceInput (2^(1+B.eval n)) i) (T.eval n) (pricePost (2^(1+B.eval n)) i)) : Spec := by
  let baseline : Polynomial ℕ := X+B+T+3
  let width := scalarPolynomial B T baseline baseline Cr
  let f := joined init serve p B T
  refine ⟨decisionProgram f subspaceGuard work,decisionTime f subspaceGuard work,width,?_⟩
  intro r s hn D E hD hE orth
  let n := r+s
  let xs := MinorLog.entries D++MinorLog.entries E
  let L := inputSize D E
  let H := baseline.eval L
  let W := width.eval L
  let Q := ∃ z∈Submodule.span ℚ (Set.range D.row),0 ≤ z ∧ 0<z ⟨0,hn⟩
  have len : xs.length=n^2 := by
    rw [show xs=rawWords D E from (rawWords_rational D E).symm,rawWords_length]
    dsimp only [n];rw [pow_two,Nat.add_mul]
  have nL : n ≤ L := Nat.le_add_right ..
  have inL : totalBits xs ≤ L := Nat.le_add_left ..
  obtain ⟨S,program,clk,bits,serviceHeight,restartBudget,initial,done⟩ := services r s D E
  have hS : S.height ≤ H := by
    calc S.height = B.eval (totalBits xs) := serviceHeight
         _ ≤ B.eval L := poly_mono B inL
         _ ≤ H := by simp only [H,baseline,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat];omega
  have arg : T.eval n+3 ≤ H := by
    have mono := poly_mono T nL
    simp only [H,baseline,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  have entries : ∀ i j,ratBits (D i j) ≤ H := by
    intro i j
    have member : D i j∈xs := List.mem_append_left _ (matrixEntry_mem D i j)
    apply (PrimalDual.ratBits_le_totalBits_of_mem member).trans
    simp only [H,baseline,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  have rc : S.restartBudget ≤ (restartPolynomial Cr).eval n := by
    rw [restartBudget];exact restartPolynomial_bound Cr n
  have room : H+(S.restartBudget+1)*((T.eval n+1)*geometricIncrement r s n H S.outputBits) ≤ W := by
    rw [bits]
    exact scalarPolynomial_bound B T baseline baseline Cr r s n L H H S.restartBudget rfl nL le_rfl le_rfl rc
  have hw : H ≤ W := (Nat.le_add_right ..).trans room
  have safe : (start [r,s] xs).memory.AllData (fun q => ratBits q ≤ W) := by
    obtain ⟨_,_,states,trace,_,size⟩ := initial
    intro i
    have hi := size 0 i
    rw [trace.1] at hi
    exact (hi.trans hS).trans hw
  have zeroSafe : ratBits (0:ℚ) ≤ W :=
    (show ratBits (0:ℚ) ≤ 3 by decide).trans ((by omega : 3 ≤ H).trans hw)
  obtain ⟨k,hk,tr,executed,flag,test,halt,allWidth⟩ := decision_run f subspaceGuard work r s xs
    (fun q => ratBits q ≤ W) Q len safe zeroSafe (by
      intro vm headers
      obtain ⟨out,physical,equation⟩ := joined_run hn D E hD hE orth init serve p B T Cr H W S
        program clk bits hS rc initial done (learner n ⟨0,hn⟩) arg entries room vm headers
      exact ⟨out,physical.mono (duration n),equation⟩)
  refine ⟨k,hk,tr,executed,⟨flag,?_,test⟩,allWidth⟩
  cases flag <;> exact halt


/-- The literal rational program at the manuscript's restart coefficient.
Its program and clock fields reduce to the corresponding fields of the
ordered-field construction with the same initializer, learner and clock. -/
noncomputable def fixedRationalSpec (init serve : Program) (p : BitProgram) (B T work : Polynomial ℕ)
    (duration : ∀ n, (joinedTime p B T 15).eval n ≤ work.eval n)
    (services : ∀ r s (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ),
      FixedServiceAt init serve B 15 D E)
    (learner : ∀ n (i : Fin n) (f : Transcript → Word → Bool), p.ComputesWithin (fun h w => [f h w])
      (priceInput (2^(1+B.eval n)) i) (T.eval n) (pricePost (2^(1+B.eval n)) i)) : Spec :=
  fixedRationalSpecWithRestarts init serve p B T work 15 duration services learner

/-- A finite rational RAM solves every ordinary marked subspace instance from
its dimension header and two matrices. Both public numerical primitives are
chosen before the input, with their original adaptive-time guarantees. -/
theorem normal_decision_of_primitives (marked : ExtremalSignRecovery) (minor : OnlineMinorLogCompression) :
    Nonempty Spec := by
  obtain ⟨p,learnerC,learnerE,learns⟩ := marked
  obtain ⟨init,serve,coef,degree,Cr,compresses⟩ := service_of_online minor
  let B : Polynomial ℕ := C coef*(X+1)^degree
  let T := learnerBound B learnerC learnerE
  have shape (x : ℕ) : B.eval x = coef*(x+1)^degree := by simp [B]
  have services (r s : ℕ) (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ) :
      FixedServiceAt init serve B Cr D E := by
    obtain ⟨S,program,clock,bits,height,restarts,run,tag⟩ := compresses r s D E
    exact ⟨S,program,clock.trans (shape _).symm,bits.trans (shape _).symm,
      height.trans (shape _).symm,restarts,run,tag⟩
  exact ⟨fixedRationalSpecWithRestarts init serve p B T (joinedTime p B T Cr) Cr
    (fun _ => le_rfl) services (fun _ i f => learnerBound_spec B learnerC learnerE learns i f)⟩

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
