import OAI.Optimization.LinearProgramming.Lattice.LLLBitLoopNative
import OAI.Optimization.LinearProgramming.Lattice.LLLBitSpace
import OAI.Optimization.LinearProgramming.Lattice.BitInitialState
import OAI.Optimization.LinearProgramming.Lattice.BitSwapNative

/-! A closed finite bit-stack program for integral lattice-basis reduction. Its time and
width clocks are computed from the physical input tape. The output theorem applies
to every independent integral basis of positive rank. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Hex.Internal

/-- Output matrix of the finite clocks and actual signed-integer transitions. -/
noncomputable def lllRows (a : IntMatrix) : IntMatrix :=
  (runOuter intMatrixCode stateCode initState (packedOuter (fun c => swapStep c.1 c.2)) lllTime lllSpace a).1

/-- The fixed Boolean stack program. Its `bound` and `runs` fields are a polynomial
worst-case bit-step bound and a complete execution certificate on every input table. -/
noncomputable def lllRowsP : Procedure intMatrixCode intMatrixCode lllRows :=
  basisP.comp (runOuterP initStateP (packedOuterP swapStepP) lllTime lllSpace)

/-- The single, dimension-independent bit-stack program returns the exact native
reduction for every independent integral row basis of positive rank. -/
theorem lllRows_packMatrix_succ {n m : ℕ} (b : Hex.Matrix ℤ (n+1) m) (hi : b.independent) :
    lllRows (packMatrix b) = packMatrix (Hex.lllNative b (3/4) (hn := by omega)) := by
  let a := packMatrix b
  let L := (intMatrixCode a).length
  let cap := lllSpace.eval L
  let T := lllTime.eval L
  let c := initialReductionCursor b (by omega)
  let exchange (x : Cursor) := swapStep x.1 x.2
  have start : (cap,1,initState a) = packCursor cap c := by
    rw [show initState a = packState (LLLState.ofBasis b) from initState_packMatrix b]
    rfl
  have sweep (d : ReductionCursor (n+1) m) (hc : c.Reaches d) (hk : d.index < n+1) :
      packedSweep (cap,d.index,packState d.state) = packState (d.state.sizeReduce d.index) := by
    let k : Fin (n+1) := ⟨d.index,hk⟩
    apply packedSweep_correct d.state k cap
    · exact hk.le.trans (packedCursor_rows_le d.state d.index)
    · intro v hv
      exact passFrame_fits b hi hc k v.2 (Or.inr ⟨v.1,hv⟩) (v.1.val+1) d.index v.1.isLt d.bounded
    · exact passFrame_fits b hi hc k _ (Or.inl (sizeReduceColumnTrace_result d.state k).symm)
        0 d.index (Nat.zero_le _) d.bounded
  have swap (d : ReductionCursor (n+1) m) (_ : d.index < n+1) :
      exchange (d.index,packState (d.state.sizeReduce d.index)) = packState ((d.state.sizeReduce d.index).swapStep d.index) :=
    swapStep_packState _ _
  have simulated (i : ℕ) : (packedOuter exchange)^[i] (cap,1,initState a) =
      packCursor cap ((hold^[i]) c) := by
    rw [start]
    exact packedOuter_iterate c cap exchange sweep swap i
  have fit (i : ℕ) (_ : 0 < i) (_ : i ≤ T) :
      (outerCode stateCode (((packedOuter exchange)^[i]) (cap,1,initState a))).length ≤
      (Polynomial.C 4*lllSpace+4).eval L := by
    rw [simulated]
    let d := hold^[i] c
    have hd : (cursorCode (d.index,packState d.state)).length ≤ cap :=
      reachableCursor_fits b hi (initial_reaches_hold c i)
    change (prodCode unaryCode cursorCode (cap,d.index,packState d.state)).length ≤ _
    rw [show (prodCode unaryCode cursorCode (cap,d.index,packState d.state)).length =
        2*cap+(cursorCode (d.index,packState d.state)).length+1 from by
          simp [prodCode,pairBits_length,unaryCode]]
    calc
      _ ≤ 4*cap+4 := by omega
      _ = _ := by simp [cap]
  unfold lllRows
  rw [runOuter_exact intMatrixCode stateCode initState (packedOuter exchange) lllTime lllSpace a fit]
  change (((packedOuter exchange)^[T]) (cap,1,initState a)).2.2.1 = _
  rw [simulated]
  change packMatrix (((hold^[T]) c).state.b) = _
  rw [lllTime_result b (by omega) hi]

theorem lllRows_packMatrix {n m : ℕ} (b : Hex.Matrix ℤ n m) (hn : 1 ≤ n) (hi : b.independent) :
    lllRows (packMatrix b) = packMatrix (Hex.lllNative b (3/4) (hn := hn)) := by
  cases n with
  | zero => omega
  | succ n => exact lllRows_packMatrix_succ b hi

/-- The ordinary bit-stack execution relation, with its exact input and output stores
and a polynomial bound in the physical encoding length. -/
theorem lllRows_native_runs {n m : ℕ} (b : Hex.Matrix ℤ n m) (hn : 1 ≤ n) (hi : b.independent) :
    ∃ steps, steps ≤ lllRowsP.bound.eval (intMatrixCode (packMatrix b)).length ∧
      Runs lllRowsP.program (singletonStore lllRowsP.input (intMatrixCode (packMatrix b)))
        (singletonStore lllRowsP.output (intMatrixCode (packMatrix (Hex.lllNative b (3/4) (hn := hn))))) steps := by
  simpa only [lllRows_packMatrix b hn hi] using lllRowsP.runs (packMatrix b)

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
