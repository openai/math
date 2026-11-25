import OAI.Optimization.LinearProgramming.Recovery.MaskedDecision
import OAI.Optimization.LinearProgramming.Recovery.SupportBundleContext
import OAI.Optimization.LinearProgramming.Recovery.SupportContext
import OAI.Optimization.LinearProgramming.RAM.CallableWindow
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant

/-! During the coordinate scan, the immutable opposite basis is immediately before
the changing flags. Thus every native test receives its complete ordinary input from
one raw window, and the numerical call preserves all caller data except its bit tag. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportBundle
open RAM RAM.Callable Geometry Matrix SupportRAM

variable {h n : ℕ}

noncomputable def invoke (solver : NormalSubspace.Spec) : Fragment :=
  .stage (.invoke (MaskedDecision.program solver) 2 (Odd.sink (.index 154)))

noncomputable def callClock (solver : NormalSubspace.Spec) (h n cap : ℕ) :=
  19*cap+225+(2*(MaskedDecision.clockPolynomial solver).eval (h+n)+2)

noncomputable def footprint (solver : NormalSubspace.Spec) (h n : ℕ) :=
  max (addressBudget (MaskedDecision.program solver)) (max (h*n+n) (max 2 (h+n)))+(MaskedDecision.clockPolynomial solver).eval (h+n)

theorem actual_call (solver : NormalSubspace.Spec) (E : Matrix (Fin h) (Fin n) ℚ) (side : Bool)
    (src cap e W : ℕ) (hn : 0 < n) (three : 3 ≤ e) (rows : ∀i j,ratBits (E i j) ≤ e)
    (height : (MaskedDecision.heightPolynomial solver).eval (h+n+e) ≤ W) (safeZero : 3 ≤ W)
    (fits : footprint solver h n < cap) (packet : h*n+n ≤ cap) (two : 2 ≤ cap)
    (oracle : Finset (Fin n)→Bool) (correct : ∀S,oracle S=true ↔ ∃z∈LinearMap.ker (maskedEquations E S).mulVecLin,0 ≤ z ∧ 0 < z ⟨0,hn⟩) :
    ContextRealizes (invoke solver) (fun z=>ratBits z ≤ W) (fun m=>Footprint (cap-1) (m.atPC 0))
      (Context E side src cap) (src+h*n) (callClock solver h n cap) oracle := by
  intro j S native caller old ns cs layout ctx
  obtain ⟨k,hk,tr,run,⟨b,halt,valid⟩,bounded⟩:=MaskedDecision.program_spec solver E S hn e three rows
  have meaning : (b=true) ↔ oracle S=true:=valid.trans (correct S).symm
  have bit : b=oracle S:=Bool.eq_iff_iff.mpr meaning
  have safe (i q):ratBits ((tr i).data q) ≤ W:=(bounded i q).trans height
  have tag : b.toNat < 2:=by cases b <;> decide
  have stage:=Odd.invoke_packed 2 (.index 154) (fun z=>ratBits z ≤ W) caller [h,n] (MaskedInput.bundle E S) tr tag cs run safe halt
    (show (caller.putIndex 154 b.toNat).AllData (fun z=>ratBits z ≤ W) from cs)
  have real:=Fragment.stage_of_run (native.atPC 0) caller src 512 (cap-1) cap (MaskedInput.bundle E S) [h,n]
    (ctx.raw layout) cs ns (show ratBits (0:ℚ) ≤ W from safeZero) old (by omega) (by simpa [MaskedInput.bundle] using packet) (by simpa using two) stage
  have fresh:=nativeWindow_trace run hk
  have fcap : nativeWindow (MaskedDecision.program solver) [h,n] (MaskedInput.bundle E S)+(MaskedDecision.clockPolynomial solver).eval (h+n) ≤ cap-1 := by
    have le : footprint solver h n ≤ cap-1:=by omega
    simpa [footprint,nativeWindow,MaskedInput.bundle] using le
  refine ⟨(tr (Fin.last k)).memory,fresh.mono fcap,safe _,?_⟩
  rw [←bit]
  exact real.mono (by unfold callClock;omega)

end SupportBundle
end Recovery
end LinearProgramming
end Optimization
end OAI
