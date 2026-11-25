import OAI.Optimization.LinearProgramming.Recovery.PrincipalHeight
import OAI.Optimization.LinearProgramming.Recovery.InitialOrientation
import OAI.Optimization.LinearProgramming.RAM.SafeRun

/-! The numerator/denominator width and all instruction clocks are fixed before
both dimensions and coefficients. The public trace begins with the ordinary RAM
bootstrap, which builds the encoded register banks from the raw input tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM RAM.Callable Geometry Polynomial

noncomputable def fragment (s : NormalSubspace.Spec) : Fragment :=
  (InitialOrientation.program s).seq ((searchWitness s).seq finish)

instance fragmentAccess (s : NormalSubspace.Spec) : Fragment.FixedAccess (fragment s) := by unfold fragment;infer_instance

set_option maxHeartbeats 750000 in
theorem fragment_run {m d : ℕ} (s : NormalSubspace.Spec) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (hm : 0 < m) (hd : 0 < d) :
    ∃ z,(fragment s).Run (fun q=>ratBits q ≤ (workerHeight s).eval (m+d+totalBits (lpInput A b)))
      (Odd.memory (start [] ([] : List ℚ)).memory (start [m,d] (lpInput A b)).memory) ((workerClock s).eval (m+d)) z ∧ Published A b z := by
  let L:=totalBits (lpInput A b)
  let seed:=(seedPolynomial s).eval (m+d+L)
  let H:=(workerHeight s).eval (m+d+L)
  let cap:=capacity s m d
  let lim:=(InitialOrientation.finalAddresses s).eval (m+d)
  let raw:=PublicInput.sourceBase m d
  obtain ⟨h,E,src,native,caller,choose,orientation⟩:=InitialOrientation.program_run s A b
  obtain ⟨three,hE,hStart⟩:=seed_bounds s (m+d+L)
  have nativeSafe : native.AllData (fun q=>ratBits q ≤ seed):=fun j=>(orientation.nativeSafe j).trans hStart
  have callerSafe : caller.AllData (fun q=>ratBits q ≤ seed):=fun j=>(orientation.callerSafe j).trans hStart
  have rawHigh : 256 ≤ raw:=by unfold raw PublicInput.sourceBase;omega
  obtain ⟨next,out,recov,foot,ready,ns,cs,addr⟩:=searchWitness_run s A b E raw src seed lim native caller orientation.height three
    (fun i j=>(orientation.entries i j).trans hE) orientation.kernel rawHigh orientation.afterInput orientation.addresses nativeSafe callerSafe
    orientation.footprint orientation.context orientation.original orientation.source orientation.rows orientation.cols
  let B:=scanWidth s h (m+1) seed
  have seedLe : seed ≤ B:=le_max_left ..
  have finalWidth : PrimalOutput.outputWidth m d B ≤ H:=finish_height_le s m d h L orientation.height
  have widen : B ≤ H:=(show B ≤ PrimalOutput.outputWidth m d B by unfold PrimalOutput.outputWidth;omega).trans finalWidth
  have indices (j) : out.index j ≤ (searchAddresses s).eval (m+d):=(addr j).trans (search_limit_le s m d h orientation.height)
  obtain ⟨_,two,space⟩:=capacity_inputs s m d h orientation.height
  obtain ⟨z,solve,published⟩:=finish_run A b next out raw (src+h*(m+1)+(m+1)) cap B ((searchAddresses s).eval (m+d)) hm hd
    (three.trans seedLe) ns cs foot two space ready (by omega) (by have old:=orientation.afterInput;change raw+(m*d+m) ≤ src at old;omega) indices
  have initRun:=choose.weakenData (fun _ bound=>bound.trans (hStart.trans (seedLe.trans widen)))
  have core:=recov.weakenData (fun _ bound=>bound.trans widen)
  have lastRun:=solve.weakenData (fun _ bound=>bound.trans finalWidth)
  refine ⟨z,(initRun.seq (core.seq lastRun)).mono ?_,published⟩
  have a:=search_time_le s m d h orientation.height
  have f:=finish_time_le s m d
  unfold workerClock
  simp only [Polynomial.eval_add]
  exact Nat.add_le_add_left (Nat.add_le_add a f) _

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
