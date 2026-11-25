import OAI.Optimization.LinearProgramming.PrimalDual.StageJoint
import OAI.Optimization.LinearProgramming.RAM.FrameReady

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Tape RAM.Block

/-- The real, interleaved second return. The original dimensions and saved vectors
are read independently of the second guest's writes to its own address space. -/
structure SecondReturned {d : Nat} (m : Nat) (c x₀ : Fin d → ℚ) (last : State ℚ) (w : Memory ℚ) : Prop where
  rows : w.index 41=m
  cols : w.index 43=d
  guest : ∀ i, w.data (2*i)=last.data i
  objective : ∀ i : Fin d, w.data (3+2*i.val)=c i
  point : ∀ i : Fin d, w.data (3+2*(d+i.val))=x₀ i

def secondCallCost (m d B k : Nat) :=
  8*(jointLen m d+2*d)+12*cutoff m d B+4*rowCount m d+4*(d+m)+21+2*k

theorem invokeJoint {m d B H k pc tag : Nat} {original target : Program} {ret : Nat → Nat}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c x₀ : Fin d → ℚ)
    (u : Memory ℚ) (safe : Good (fun q => ratBits q≤H) u) (hz : 3≤H) (r : JointReady A b c x₀ B u)
    (placed : CodeAt target pc (Call.prepareCallInputs.compile pc))
    (callee : CodeAt target (pc+Call.prepareCallInputs.size) (Call.subroutine original
      (pc+Call.prepareCallInputs.size) ret))
    (tr : Fin (k+1) → State ℚ)
    (oracle : Trace original (start [rowCount m d,d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))) k tr)
    (oracleSafe : ∀ i, scalarBound H (tr i)) (done : (tr (Fin.last k)).output=some tag) :
    ∃ l ≤ secondCallCost m d B k, ∃ w, Execution target (scalarBound H) (u.atPC pc) l
      (w.atPC (ret tag)) ∧ SecondReturned m c x₀ (tr (Fin.last k)) w := by
  let input := lpInput (finJointMatrix A b c) (finJointRhs b c)
  have len : input.length=jointLen m d := lpInput_length _ _
  have enough := (origin_above m d).1
  obtain ⟨v,run₁,ve,vi,vs,_,vh⟩ := Call.prepareCallInputs_correct u (rowCount m d) (d+m)
    (jointBase m d) (origin m d+m*d+m) (2*d) (cutoff m d B) input safe
    (show ratBits 0 ≤ H from hz) r.rows r.cols r.inputBase (r.inputSize.trans len.symm) r.savedBase
    r.savedSize r.limit (by rw [len]; unfold jointBase; omega) (by rw [len]; omega)
    r.dataTail r.indexTail (fun i hi => r.input i (len ▸ hi))
  obtain ⟨l,hl,w,run₂,we,_,wo,wi⟩ := Call.invoke_prepared_trace v [rowCount m d,d+m] input
    (fun q => ratBits q ≤ H) callee ve vi run₁.safe_end tr oracle oracleSafe done
  have perm41 : w.index 41=m := (wi 20).trans ((vh 41 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans r.originalRows)
  have perm43 : w.index 43=d := (wi 21).trans ((vh 43 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans r.originalCols)
  have pair (i : Nat) (hi : i<2*d) : w.data (3+2*i)=((List.ofFn c ++ List.ofFn x₀)[i]?).getD 0 := by
    have odd := wo (i+1)
    rw [show 2*(i+1)+1=3+2*i by omega] at odd
    exact odd.trans ((vs i hi).trans (r.saved i hi))
  obtain ⟨wc,wx⟩ := savedPair_secondWindow c x₀ w pair
  exact ⟨_,by unfold secondCallCost; rw [len]; omega,w,
    (run₁.compile_correct placed).append run₂,⟨perm41,perm43,we,wc,wx⟩⟩

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
