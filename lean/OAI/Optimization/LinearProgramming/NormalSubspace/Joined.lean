import OAI.Optimization.LinearProgramming.NormalSubspace.Boot
import OAI.Optimization.LinearProgramming.NormalSubspace.FiniteRun
import OAI.Optimization.LinearProgramming.Recovery.SubspaceBounds
import OAI.Optimization.LinearProgramming.Recovery.SubspaceAccess

/-! Use the initialized minor service and the finite price learner on the same
physical machine, and account for the initialization, restarts and final read. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace

open RAM RAM.Callable OracleSpec Matrix Geometry Geometry.BorderBatch Recovery.PackedPCG Recovery.OracleInline Polynomial
open scoped Matrix

noncomputable def joined (init minor : Program) (p : BitProgram) (B T : Polynomial ℕ) : Fragment :=
  .seq (numericCall (numericInitialize init (T.eval 1) T.natDegree)) (subspaceKernel p B minor)

instance (init minor : Program) (p : BitProgram) (B T : Polynomial ℕ) :
    Fragment.FixedAccess (joined init minor p B T) := by
  unfold joined numericCall
  infer_instance

noncomputable def joinedTime (p : BitProgram) (B T : Polynomial ℕ) (restartConstant : ℕ) : Polynomial ℕ :=
  2*(numericInitPolynomial (T.eval 1) T.natDegree B+1)+2+subspaceTimePolynomial p B T restartConstant

private theorem widenRun {f : Fragment} {a b : Memory ℚ} {cost fromBound toBound : ℕ}
    (run : f.Run (fun q => ratBits q ≤ fromBound) a cost b) (width : fromBound ≤ toBound) :
    f.Run (fun q => ratBits q ≤ toBound) a cost b := by
  intro prog pc code
  obtain ⟨k,count,trace⟩ := run prog pc code
  exact ⟨k,count,trace.weaken (fun _ h i => (h i).trans width)⟩

/-- All assumptions about subroutines here are ordinary recorded initialization
and learner traces. The final result is the marked-coordinate subspace test. -/
theorem joined_run {r s : ℕ} (hn : 0 < r+s)
    (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ)
    (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (orth : D*Eᵀ=0)
    (init serve : Program) (p : BitProgram) (B T : Polynomial ℕ) (Cr H W : ℕ)
    (S : Service D E) (program : S.program=serve) (clock : S.clock=B.eval (r+s))
    (bits : S.outputBits=B.eval (r+s)) (height : S.height ≤ H)
    (restarts : S.restartBudget ≤ (restartPolynomial Cr).eval (r+s))
    (initial : MinorLog.call init S.clock S.height
      (start [r,s,r+s] (MinorLog.entries D++MinorLog.entries E)) S.ready) (done : S.ready.output=some 0)
    (learner : ∀ reply : Transcript→Word→Bool, p.ComputesWithin (fun h w => [reply h w])
      (priceInput (2^(1+B.eval (r+s))) ⟨0,hn⟩) (T.eval (r+s)) (pricePost (2^(1+B.eval (r+s))) ⟨0,hn⟩))
    (arg : T.eval (r+s)+3 ≤ H) (matrix : ∀ i j,ratBits (D i j) ≤ H)
    (room : H+(S.restartBudget+1)*((T.eval (r+s)+1)*geometricIncrement r s (r+s) H S.outputBits) ≤ W)
    (vm : Memory ℚ) (outer : OuterVM r s (start [r,s] (MinorLog.entries D++MinorLog.entries E)).memory vm) :
    ∃ out, (joined init serve p B T).Run (fun q => ratBits q ≤ W)
      (Odd.memory (Odd.memory (start [] ([]:List ℚ)).memory
        (start [r,s] (MinorLog.entries D++MinorLog.entries E)).memory) vm)
      ((joinedTime p B T Cr).eval (r+s)) out ∧
      (subspaceGuard.test out=true ↔ ∃ z∈Submodule.span ℚ (Set.range D.row),0 ≤ z ∧ 0<z ⟨0,hn⟩) := by
  let n := r+s
  let anchor : Fin n := ⟨0,hn⟩
  let raw := (start [r,s] (MinorLog.entries D++MinorLog.entries E)).memory
  have safeVM : vm.AllData (fun q => ratBits q ≤ H) := by
    obtain ⟨_,_,states,execution,_,width⟩ := initial
    intro i
    rw [congrFun outer.data i]
    have hw := width 0 i
    rw [execution.1] at hw
    exact hw.trans height
  obtain ⟨geom,setup,matrices⟩ := numericInitialize_service_under_vm init (T.eval 1) T.natDegree
    D E S vm (fun q => ratBits q ≤ H) safeVM initial done (fun _ h => h.trans height)
  have safeGeom : RowRAM.Within H geom := by
    intro i
    simpa only [Odd.data_even,Odd.data_slot] using setup.safe_end (2*Odd.slot i)
  have hw : H ≤ W := (Nat.le_add_right ..).trans room
  have ports : Ports anchor 3 (vm.putIndex 1 0) := by
    constructor
    · change 3 ≤ (vm.putIndex 1 0).index 43
      simpa using (le_of_eq outer.node.symm)
    · simpa [n] using outer.dimension
    · simpa [anchor] using outer.offset
    · simpa using outer.root
  have savedVM : RowRAM.Within W (vm.putIndex 1 0) := fun i => (safeVM i).trans hw
  have buffer : 256+T.eval n ≤ (buffers r s n (polyBound (T.eval 1) T.natDegree n)).dual := by
    change 256+T.eval n ≤ 256+n*n+polyBound (T.eval 1) T.natDegree n
    have := polynomial_eval_le_polyBound T n
    omega
  obtain ⟨out,body,correct⟩ := subspaceKernel_run S _ p B anchor (T.eval n) H H 3 W geom
    (vm.putIndex 1 0) learner bits.symm matrices safeGeom ports (by decide) savedVM
    hD hE orth rfl buffer height (height_of_call initial) arg arg matrix room
  rw [program] at body
  have total := (widenRun setup hw).seq body
  have kernelTime := subspaceTimePolynomial_bound p B T Cr r s n S.restartBudget rfl restarts
  rw [←clock] at kernelTime
  refine ⟨out,total.mono ?_,correct⟩
  simp only [joinedTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat,
    numericInitPolynomial_eval]
  dsimp only [n] at kernelTime ⊢
  rw [←clock]
  omega

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
