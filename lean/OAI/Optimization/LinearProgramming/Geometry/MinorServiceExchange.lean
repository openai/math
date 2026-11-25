import OAI.Optimization.LinearProgramming.Geometry.MinorNativeCall
import OAI.Optimization.LinearProgramming.Geometry.BorderServiceLive
import OAI.Optimization.LinearProgramming.Geometry.MinorSite

/-! Discharge the physical callback premise of the numerical RAM inliner using a
sealed service, a genuine marked query edge, and the actual canonical minor request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Callable OracleSpec OracleSpec.MinorLog Contract OracleSegments MinorInstall Matrix

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- The emitter and decoding register roles come from the run marker, and the valid
minor comes from the caller's recorded transcript. The callee state is the one actually
reached on that transcript. -/
theorem Service.native_step (S : Service D E) (hist : Contract.History ℚ) (native : State ℚ)
    (live : S.Live hist native) (caller : Memory ℚ) (u : Index D E) {src len dst count : ℕ} (H : ℕ)
    (site : MinorSite caller src len dst count) (message : sentPacket caller src len=packet u.val)
    (callerSafe : ∀i,ratBits (caller.data i) ≤ H) (ready : ∀i,ratBits (S.ready.data i) ≤ S.height) :
    ∃ ans final, S.oracle hist (sentPacket caller src len)=reply ans ∧
      S.Live ((sentPacket caller src len,reply ans)::hist) final ∧
      (nativeQuery S.program).Run (fun q => ratBits q ≤ directWidth (max H S.height) r s n)
        (Odd.memory native.memory caller) (serviceClock r s n S.clock)
        (Odd.memory final.memory (received caller dst count (reply ans))) := by
  obtain ⟨source,length,destination,counter,hs,hr,_,zero2,zero29⟩ := site
  subst src len dst count
  obtain ⟨ans,final,response,call,emit,_,fresh⟩ := S.advance hist native live u
  refine ⟨ans,final,by rw [message,response],by simpa [message] using fresh,?_⟩
  have hb : ∀i,ratBits (native.data i) ≤ max H S.height := fun i => (live.height ready i).trans (le_max_right ..)
  have hc : ∀i,ratBits (caller.data i) ≤ max H S.height := fun i => (callerSafe i).trans (le_max_left ..)
  have run := nativeQuery_run u.val S.program native final caller S.clock S.height (max H S.height) ans call emit hs hr
    zero2 zero29 message hc hb
  simpa [Nat.max_assoc] using run

/-- A fixed simulation width that contains the geometric caller, the native service,
and the natural request-word counters is preserved across every invocation. -/
theorem Service.native_step_at (S : Service D E) (hist : Contract.History ℚ) (native : State ℚ)
    (live : S.Live hist native) (caller : Memory ℚ) (u : Index D E) {src len dst count : ℕ} (H : ℕ)
    (site : MinorSite caller src len dst count) (message : sentPacket caller src len=packet u.val)
    (callerSafe : ∀i,ratBits (caller.data i) ≤ H) (ready : ∀i,ratBits (S.ready.data i) ≤ S.height)
    (serviceWidth : S.height≤H) (packetWidth : r+s+n+4≤H) :
    ∃ ans final, S.oracle hist (sentPacket caller src len)=reply ans ∧
      S.Live ((sentPacket caller src len,reply ans)::hist) final ∧
      (nativeQuery S.program).Run (fun q => ratBits q ≤ H) (Odd.memory native.memory caller)
        (serviceClock r s n S.clock) (Odd.memory final.memory (received caller dst count (reply ans))) := by
  simpa only [directWidth,Nat.max_eq_left serviceWidth,Nat.max_eq_left packetWidth] using
    S.native_step hist native live caller u H site message callerSafe ready

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
