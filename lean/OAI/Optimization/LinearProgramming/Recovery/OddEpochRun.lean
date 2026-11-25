import OAI.Optimization.LinearProgramming.Recovery.OddEpochAdvance
import OAI.Optimization.LinearProgramming.Recovery.MeasuredLoop

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Tape RAM.Callable OracleSpec BitRAM
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The ordinary RAM stops on the first numerical restart or returns the actual completed
PCG output. The exact cache and every prior numerical answer are witnessed by the same
source path. The entire interpreter consumes one linear bound in the frozen bit clock. -/
theorem epochLoop_run {p : BitProgram} {bo : WordOracle} {P : K → Prop} {env : Environment K}
    {ack cut : Receipt p K} {handler : Fragment} {start last : p.Config} {budget time : ℕ}
    (service : Handles p bo P env ack cut handler start last budget)
    (source : p.Run bo start time last) (ended : last.pc=none) {native m : Memory K}
    (live : Live p P env start native m) :
    ∃ z next v, (epochLoop p handler).Run P (Odd.memory native m) (epochUnit p budget*(time+1)+5)
      (Odd.memory next v) ∧ Produced p P env last z next v ∧ ServiceTrace p bo ack cut start native z next := by
  let x : Cursor p K := ⟨start,native,time⟩
  let first := m.putIndex Dispatch.limitReg p.states
  have init := Odd.leaf_run P native live.nativeSafe (eval_constI m live.vmSafe Dispatch.limitReg p.states)
  have invariant : Active p bo P env start last x (Odd.memory native first) :=
    ⟨⟨0,.refl _⟩,source,first,rfl,live.refresh,Memory.putIndex_same _ _ _⟩
  obtain ⟨z,t,loop,done,path⟩ := Recovery.measured_loop epochGuard
    (.seq (boundary p handler) (Odd.leaf (finishCode p statusReg))) P Cursor.left (epochUnit p budget)
    (Active p bo P env start last) (Out p P env last)
    (fun x z => ServiceTrace p bo ack cut x.source x.native z.1 z.2)
    (fun _ _ h => ready_safe h) (fun _ _ h => ready_finished ack cut h)
    (fun y v h _ => epoch_advance service ended y v h) x (Odd.memory native first) invariant
  obtain ⟨v,rfl,status⟩ := done
  refine ⟨z.1,z.2,v,(init.seq loop).mono ?_,status,path⟩
  change 4*1+(epochUnit p budget*(time+1)+1) ≤ _
  omega

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
