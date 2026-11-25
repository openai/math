import OAI.Optimization.LinearProgramming.NormalSubspace.InputBits
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableResume
import OAI.Optimization.LinearProgramming.RAM.CallableWindow

/-! Call the ordinary marked-subspace program using the actual packed numerical
row matrices, and retain the exact caller bank and a bound for clearing the callee. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace
open Matrix RAM RAM.Callable OracleSpec Geometry
open scoped Matrix

def call (S : Spec) (replyReg : ℕ) : Fragment :=
  .stage (.invoke S.program 2 (Odd.sink (.index replyReg)))

def callTime (S : Spec) (cap n : ℕ) := 19*cap+225+(2*S.clock.eval n+2)

theorem call_run (S : Spec) {r s n : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (dim : r+s=n) (hn : 0 < n) (hD : LinearIndependent ℚ D.row) (hE : LinearIndependent ℚ E.row) (orth : D*Eᵀ=0)
    (caller native : Memory ℚ) (src dims cap dirty replyReg W : ℕ)
    (raw : RawTapes caller src dims cap (encodedGramInput D++encodedGramInput E) [r,s])
    (fp : Footprint dirty (native.atPC 0)) (hc : dirty < cap) (wordRoom : n*n ≤ cap) (dimRoom : 2 ≤ cap)
    (callerSafe : caller.AllData (fun z=>ratBits z ≤ W)) (nativeSafe : native.AllData (fun z=>ratBits z ≤ W)) (zero : 3 ≤ W)
    (size : S.height.eval (r+s+((MinorLog.entries D++MinorLog.entries E).map ratBits).sum) ≤ W) :
    ∃ (a : Memory ℚ) (answer : Bool),(call S replyReg).Run (fun z=>ratBits z ≤ W) (Odd.memory native caller) (callTime S cap n)
      (Odd.memory a (caller.putIndex replyReg answer.toNat)) ∧
      (answer=true ↔ ∃z∈Submodule.span ℚ (Set.range D.row),0 ≤ z ∧ 0 < z ⟨0,hn⟩) ∧
      Footprint (nativeWindow S.program [r,s] (MinorLog.entries D++MinorLog.entries E)+S.clock.eval n) (a.atPC 0) := by
  subst n
  let xs:=MinorLog.entries D++MinorLog.entries E
  obtain ⟨k,hk,tr,run,⟨answer,halt,decodes⟩,safe⟩:=S.run r s hn D E hD hE orth
  have hs (i j) : ratBits ((tr i).data j) ≤ W:=(safe i j).trans size
  have tag : answer.toNat < 2:=by cases answer <;> decide
  have callee:=Odd.invoke_packed 2 (.index replyReg) (fun z=>ratBits z ≤ W) caller [r,s] xs tr tag callerSafe run hs halt
    (show (caller.putIndex replyReg answer.toNat).AllData (fun z=>ratBits z ≤ W) from callerSafe)
  have len : xs.length=(r+s)*(r+s):=by simp only [xs,←gramEntries,List.length_append,length_encodedGramInput,Nat.add_mul]
  rw [gramEntries D,gramEntries E] at raw
  obtain ⟨work,foot⟩:=And.intro (Fragment.stage_of_run (native.atPC 0) caller src dims dirty cap xs [r,s] raw callerSafe nativeSafe
    (show ratBits (0:ℚ) ≤ W from zero) fp hc (len.symm ▸ wordRoom) (by simpa using dimRoom) callee) (nativeWindow_trace run hk)
  exact ⟨(tr (Fin.last k)).memory,answer,work.mono (by unfold callTime;omega),decodes,foot⟩

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
