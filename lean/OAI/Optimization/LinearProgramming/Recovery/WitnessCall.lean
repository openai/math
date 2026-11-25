import OAI.Optimization.LinearProgramming.Recovery.WitnessCallCode
import OAI.Optimization.LinearProgramming.Recovery.SupportBundleContext
import OAI.Optimization.LinearProgramming.Recovery.WitnessProgram
import OAI.Optimization.LinearProgramming.RAM.CallableWindow
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant

/-! Invoke the ordinary rational witness solver on the final support flags, with the
same field-independent instruction fragment and its rational register bound. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessCall
open RAM RAM.Callable RAM.Call RAM.Tape Geometry Matrix SupportRAM

variable {h n : ℕ}

theorem invoke_run (E : Matrix (Fin h) (Fin n) ℚ) (S : Finset (Fin n)) (side : Bool)
    (src cap e W step : ℕ) (hn : 0<n) (three : 3 ≤ e) (rows : ∀i j,ratBits (E i j) ≤ e) (zero : 3 ≤ W)
    (width : WitnessProgram.heightPolynomial.eval (h+n+e) ≤ W) (wordRoom : h*n+n ≤ cap) (dimRoom : 2 ≤ cap)
    (native caller : Memory ℚ) (fp : Footprint (cap-1) (native.atPC 0)) (nativeSafe : native.AllData (fun q=>ratBits q ≤ W))
    (callerSafe : caller.AllData (fun q=>ratBits q ≤ W)) (ctx : SupportBundle.Context E side src cap caller)
    (flags : Layout caller (src+h*n) step S) (w : Fin n→ℚ)
    (answer : Elimination.fixedSolve (normalizedSystem (maskedEquations E S) ⟨0,hn⟩) (Presentation.anchorRhs (h+n))=some w) :
    ∃ t,invoke.Run (fun q=>ratBits q ≤ W) (Odd.memory native caller) (numericalTime h n cap) (Odd.memory t (caller.putIndex 1 0)) ∧
      (∀j : Fin n,t.data j.val=w j) ∧ t.AllData (fun q=>ratBits q ≤ W) ∧ Footprint (numericalFootprint h n) (t.atPC 0) := by
  obtain ⟨k,hk,tr,real,tag,vector,safe⟩:=WitnessProgram.program_spec E S hn e three rows w answer
  have bounded (i j):ratBits ((tr i).data j) ≤ W:=(safe i j).trans width
  have run:=Odd.invoke_packed 1 (.index 1) (fun q=>ratBits q ≤ W) caller [h,n] (MaskedInput.bundle E S) tr (by decide : 0<1)
    callerSafe real bounded tag (show (caller.putIndex 1 0).AllData (fun q=>ratBits q ≤ W) from callerSafe)
  have call:=Fragment.stage_of_run (native.atPC 0) caller src 512 (cap-1) cap (MaskedInput.bundle E S) [h,n]
    (ctx.raw flags) callerSafe nativeSafe (show ratBits (0:ℚ) ≤ W from zero) fp (by omega) (by simpa [MaskedInput.bundle] using wordRoom) (by simpa using dimRoom) run
  have fresh:=nativeWindow_trace real hk
  refine ⟨(tr (Fin.last k)).memory,call.mono (by unfold numericalTime;omega),vector,bounded _,?_⟩
  simpa only [numericalFootprint,nativeWindow,MaskedInput.bundle,List.length_append,length_encodedGramInput,List.length_ofFn,
    List.length_cons,List.length_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using fresh

end WitnessCall
end Recovery
end LinearProgramming
end Optimization
end OAI
