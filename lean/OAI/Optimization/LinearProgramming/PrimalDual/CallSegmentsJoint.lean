import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsRoute

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace CallSegments

open RAM RAM.Call RAM.Tape RAM.Block Polynomial Bridge

/-- Stage the actual joint system, prepare its canonical guest input, and record
its single subroutine execution. The first returned point and objective survive. -/
theorem joint_parts (p : Program) (C E : ℕ) {m d H G k tag : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (first : State ℚ) (s : Memory ℚ)
    (zero : 3 ≤ H) (wide : H ≤ G) (safe : Within H s)
    (firstFrame : AfterFirst p C E m d (lpInput A b) (List.ofFn c) first s)
    (tr : Fin (k+1) → State ℚ)
    (guestRun : Trace p (start [rowCount m d,d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))) k tr)
    (bounds : ∀ i, scalarBound H (tr i))
    (valid : FeasibilityOutput (finJointMatrix A b c) (finJointRhs b c) (tr (Fin.last k)))
    (tagged : (tr (Fin.last k)).output = some tag) :
    let B := firstLimit p C E m d
    let off := firstReturnBase p C E
    ∃ n ≤ stageBudget.eval (m+d+B)+secondCallCost m d B k, ∃ after,
      Joined (program p C E) p G (jointParts p C E A b c tag) (s.atPC (firstReturn off 0)) n
        (after.atPC (endingBlocks.secondRet off tag)) ∧ Within H after ∧
      SecondReturned m c (readVector first 0 d) (tr (Fin.last k)) after := by
  intro B off
  let x₀ := readVector first 0 d
  let input := lpInput (finJointMatrix A b c) (finJointRhs b c)
  have len : input.length = jointLen m d := lpInput_length _ _
  have olen : (lpInput A b++List.ofFn c).length = origLen m d := by simp [lpInput_length,origLen]
  obtain ⟨u,j,stage,hj,ready⟩ := stageJoint_correct A b c x₀ s safe zero
    firstFrame.rows firstFrame.cols firstFrame.limit
    (fun i hi => firstFrame.original i (by simpa only [olen] using hi))
    (fun i => by simpa [x₀,readVector] using firstFrame.result i.val)
    (fun i hi => (firstFrame.vacant (2*i) (by change 2*B+2 ≤ 2*i; omega)).1)
    (fun i hi => (firstFrame.vacant (2*i) (by change 2*B+2 ≤ 2*i; omega)).2)
  have enough := (origin_above m d).1
  obtain ⟨v,prep,ve,vi,vs,_,vh⟩ := prepareCallInputs_correct u (rowCount m d) (d+m)
    (jointBase m d) (origin m d+m*d+m) (2*d) (cutoff m d B) input stage.safe_end
    (show ratBits (0:ℚ) ≤ H from zero) ready.rows ready.cols ready.inputBase (ready.inputSize.trans len.symm)
    ready.savedBase ready.savedSize ready.limit (by rw [len]; unfold jointBase; omega) (by rw [len]; omega)
    ready.dataTail ready.indexTail (fun i hi => ready.input i (len ▸ hi))
  have place := EndBlocks.placed (bs:=endingBlocks) (withFirstCall_locations p C E firstReturn (endingCode p)).2.2
  obtain ⟨l,hl,after,call,frame⟩ := record (valid:=FeasibilityOutput (finJointMatrix A b c) (finJointRhs b c))
    v place.callee ve vi prep.safe_end tr guestRun bounds valid tagged
  have rows : after.index 41 = m := (frame.callerIndex 20).trans ((vh 41 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans ready.originalRows)
  have cols : after.index 43 = d := (frame.callerIndex 21).trans ((vh 43 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans ready.originalCols)
  have pair (i : ℕ) (hi : i < 2*d) : after.data (3+2*i) = ((List.ofFn c++List.ofFn x₀)[i]?).getD 0 := by
    have saved := frame.callerData (i+1)
    rw [show 2*(i+1)+1 = 3+2*i by omega] at saved
    exact saved.trans ((vs i hi).trans (ready.saved i hi))
  obtain ⟨wc,wx⟩ := savedPair_secondWindow c x₀ after pair
  have firstPart := Realizes.fixed (guest:=p) place.stage (widenBlock stage wide)
  have setupPart := Realizes.fixed (guest:=p) place.prepare (widenBlock prep wide)
  have parts := Joined.cons firstPart (Joined.cons setupPart (Joined.single (Realizes.embedded (record_widen call wide))))
  refine ⟨_,?_,after,parts,call.physical.safe_end,rows,cols,frame.data,wc,wx⟩
  apply Nat.add_le_add hj
  unfold secondCallCost
  rw [len]
  omega

end CallSegments
end PrimalDual
end LinearProgramming
end Optimization
end OAI
