import OAI.Optimization.LinearProgramming.Recovery.OracleInline
import OAI.Optimization.LinearProgramming.Geometry.MinorServiceExchange

/-! Close the generic ordinary-RAM inliner at a genuine persistent signed-minor
service. A physical caller query must carry its actual indexed packet and the live
geometric transfer registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace OracleInline

open Matrix RAM RAM.Callable Contract OracleSpec
open _root_.OAI.Optimization.LinearProgramming.Geometry.OracleSegments
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Geometry.MinorInstall

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def namedMinor (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) : QueryMark ℚ :=
  fun mem src len dst count => MinorSite mem src len dst count ∧
    ∃ u : MinorLog.Index D E,sentPacket mem src len=packet u.val

def minorHandler (p : Program) : Handler := fun _ _ _ _=>nativeQuery p

def cache (S : Service D E) (hist : History ℚ) (m : Memory ℚ) : Prop :=
  ∃ st : State ℚ,st.memory=m ∧ S.Live hist st

/-- Each genuine `.query` executes the declared fixed `S.program`, mutates its own
native generator state, writes the literal reply, and returns to its relocated caller. -/
theorem minorHandler_handles (S : Service D E) (H : ℕ) (cacheWidth : S.height ≤ H) (scratch : r+s+n+4 ≤ H)
    (ready : ∀ i,ratBits (S.ready.data i) ≤ S.height) :
    Handles (minorHandler S.program) (namedMinor D E) S.oracle (fun x=>ratBits x ≤ H) (cache S)
      (serviceClock r s n S.clock) := by
  intro c e hist src len dst count safe _ cacheOK site
  obtain ⟨st,rfl,live⟩:=cacheOK
  obtain ⟨marked,u,packetOK⟩:=site
  obtain ⟨ans,final,response,live',execution⟩:=S.native_step hist st live c u H marked packetOK safe ready
  have hwidth : directWidth (max H S.height) r s n=H := by simp [directWidth,max_eq_left cacheWidth,max_eq_left scratch]
  rw [hwidth] at execution
  refine ⟨final.memory,?_,?_,?_⟩
  · intro i
    simpa only [Odd.data_even] using execution.safe_end (2*i)
  · exact ⟨final,rfl,response.symm ▸ live'⟩
  · exact response.symm ▸ execution

/-- Complete inlining of a terminating marked geometric ROM, including its first
interruption or successful end. No placeholder oracle transition remains in the result. -/
theorem minor_program_runs (S : Service D E) (H : ℕ) (maxHeight : S.height ≤ H) (scratch : r+s+n+4 ≤ H)
    (ready : ∀ i,ratBits (S.ready.data i) ≤ S.height) (source : OracleProgram) (Q : Memory ℚ→Prop)
    (bounded : ∀ m,Q m→m.AllData (fun x=>ratBits x ≤ H)) (caller native : Memory ℚ) (hist : History ℚ)
    (safe : native.AllData (fun x=>ratBits x ≤ H)) (live : cache S hist native) {k : ℕ} {last : Config ℚ}
    (sourceRun : MarkedRun (namedMinor D E) source S.oracle Q ⟨caller.atPC 0,hist⟩ k last)
    (done : last.state.output.isSome=true) :
    ∃ native',cache S last.history native' ∧ native'.AllData (fun x=>ratBits x ≤ H) ∧
      (fragment source (minorHandler S.program)).Run (fun x=>ratBits x ≤ H) (Odd.memory native caller)
        (k*(max 4 (serviceClock r s n S.clock))) (Odd.memory native' last.state.memory) := by
  obtain ⟨next,width,live',run⟩:=fragment_runs (minorHandler_handles S H maxHeight scratch ready) bounded caller native hist safe live sourceRun done
  exact ⟨next,live',width,run⟩

end OracleInline
end Recovery
end LinearProgramming
end Optimization
end OAI
