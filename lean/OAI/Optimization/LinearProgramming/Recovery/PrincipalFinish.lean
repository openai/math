import OAI.Optimization.LinearProgramming.Recovery.FinalPrimal
import OAI.Optimization.LinearProgramming.Recovery.FinalDual
import OAI.Optimization.LinearProgramming.Recovery.PrincipalWitnessReady
import OAI.Optimization.LinearProgramming.Recovery.Output

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal
open RAM RAM.Callable Geometry Matrix

private def sideGuard : Cond := Odd.cond (.addrLT 159 156)
def finish : Fragment := (Odd.leaf (.op (.addrConst 159 0))).seq (.branch sideGuard PrimalOutput.program DualOutput.program)
noncomputable def finishTime (m d cap limit : ℕ) := 16+PrimalOutput.programTime m d cap limit+(8+Publish.oddTime m)

instance finishAccess : Fragment.FixedAccess finish:=by
  unfold finish DualOutput.program Odd.leaf
  infer_instance

theorem finish_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) (native caller : Memory ℚ)
    (raw atW cap seed limit : ℕ) (hm : 0 < m) (hd : 0 < d) (three : 3 ≤ seed) (old : native.AllData (fun q=>ratBits q ≤ seed))
    (safe : caller.AllData (fun q=>ratBits q ≤ seed)) (foot : Footprint (cap-1) (native.atPC 0)) (two : 2 ≤ cap) (words : (d+1)*m ≤ cap)
    (ready : WitnessReady A b raw atW cap caller) (lo : 7 ≤ raw) (sep : raw+(m*d+m) ≤ atW) (bounded : ∀j,caller.index j ≤ limit) :
    ∃ z,finish.Run (fun q=>ratBits q ≤ PrimalOutput.outputWidth m d seed) (Odd.memory native caller) (finishTime m d cap limit) z ∧ Published A b z := by
  let v:=caller.putIndex 159 0
  let W:=PrimalOutput.outputWidth m d seed
  have lower : seed ≤ W:=by dsimp [W,PrimalOutput.outputWidth];omega
  have ns : native.AllData (fun q=>ratBits q ≤ W):=fun j=>(old j).trans lower
  have cs : caller.AllData (fun q=>ratBits q ≤ W):=fun j=>(safe j).trans lower
  have zero:=Odd.leaf_run (fun q=>ratBits q ≤ W) native ns (Block.Eval.op_addrConst (safe:=Memory.AllData (fun q=>ratBits q ≤ W)) caller 159 0 cs cs)
  have hbound (j : ℕ) : v.index j ≤ limit:=by by_cases h : j=159 <;> simp [v,Memory.putIndex,h,bounded]
  have flag : sideGuard.test (Odd.memory native v)=(ref A b).primal:=by
    rw [sideGuard,Odd.cond_test]
    cases h : (ref A b).primal <;> simp [Cond.test,v,Memory.putIndex,ready.side,h]
  cases orient : (ref A b).primal with
  | false =>
    obtain ⟨hy,norm⟩:=dual_point A b orient
    obtain ⟨z,publish,out,tag,nil⟩:=DualOutput.program_run native v (ref A b).point atW W (by simpa [v,Memory.putIndex] using ready.rows)
      (by simpa [v,Memory.putIndex] using ready.point) (by omega) hm ready.vector ns cs
    have branch:=Fragment.Run.branchFalse (flag.trans orient) PrimalOutput.program publish
    exact ⟨z,(zero.seq branch).mono (by unfold finishTime;omega),.infeasible _ hy norm out tag nil⟩
  | true =>
    obtain ⟨x,solution,hx⟩:=primal_point A b orient
    obtain ⟨z,publish,out,tag,nil⟩:=PrimalOutput.program_run A b (ref A b).point native v raw atW cap seed limit hm hd three old safe foot two words
      ready.original ready.vector lo sep hbound (by simpa [v,Memory.putIndex] using ready.source) (by simpa [v,Memory.putIndex] using ready.rows)
      (by simpa [v,Memory.putIndex] using ready.columns) (by simpa [v,Memory.putIndex] using ready.capacity) (by simpa [v,Memory.putIndex] using ready.point) x solution
    have branch:=Fragment.Run.branchTrue (flag.trans orient) publish DualOutput.program
    exact ⟨z,(zero.seq branch).mono (by unfold finishTime;omega),.feasible x hx out tag nil⟩

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI
