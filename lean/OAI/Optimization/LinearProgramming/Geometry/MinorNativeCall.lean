import OAI.Optimization.LinearProgramming.Geometry.MinorExactInstall
import OAI.Optimization.LinearProgramming.Geometry.MinorNativeReply
import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableResume

/-! A physical realization of one scalar geometric query with its actual persistent
compression routine, including the restarting exit, packet words, and register frames. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Callable OracleSpec OracleSpec.MinorLog OracleSegments Contraction.Machine

/-- The native program is fixed once. Its two halting tags enter the corresponding
value or restarting reply branches. -/
def nativeQuery (program : Program) : Fragment := (Fragment.ofBlock exactStage).seq
  ((Fragment.invoke program 2 (Odd.sink responseSink)).seq (Fragment.ofBlock replyBlock))

def serviceClock (r s n clock : ℕ) : ℕ := directClock r s n + 2*clock+44

/-- All work outside the two-instruction simulation of each service step is
quadratic in the dimensions of the packet domain. -/
theorem serviceClock_le (r s n clock : ℕ) :
    serviceClock r s n clock ≤ 208*(r+s+n+1)^2+2*clock := by
  unfold serviceClock directClock
  ring_nf
  omega

/-- A single physical fragment realizes the abstract query against the running native
service. Every odd caller register is restored except for the specified reply cells. -/
theorem nativeQuery_run {r s n : ℕ} (u : RawIndex r s n) (program : Program)
    (current final : State ℚ) (caller : Memory ℚ) (clock height H : ℕ) (ans : Option ℚ)
    (record : MinorLog.call program (clock-(words u).length) height (MinorLog.resume current (words u)) final)
    (emitted : MinorLog.emits final ans) (hsrc : 35 ≤ caller.index 80)
    (recv : 35 ≤ caller.index 82) (c2 : caller.data 2=0) (c29 : caller.data 29=0)
    (packet : registerPacket (caller.atPC 0) 80 81=BorderBatch.packet u)
    (incoming : ∀i,ratBits (caller.data i) ≤ H) (past : ∀i,ratBits (current.data i) ≤ H) :
    (nativeQuery program).Run (fun q => ratBits q ≤ directWidth (max H height) r s n)
      (Odd.memory current.memory caller) (serviceClock r s n clock)
      (Odd.memory final.memory (received caller 82 83 (BorderBatch.reply ans))) := by
  let P := fun q : ℚ => ratBits q ≤ directWidth (max H height) r s n
  obtain ⟨prepCost,sc,prepared⟩ := exactStage_eval u current caller (max H height) hsrc c2 c29 packet
    (fun i => (incoming i).trans (le_max_left ..)) (fun i => (past i).trans (le_max_left ..))
  have kept : caller.AllData P := fun i => (incoming i).trans ((le_max_left H height).trans (le_max_left ..))
  have hz : P 0 := by change 3 ≤ max (max H height) (r+s+n+4); omega
  have ho : P 1 := by change 3 ≤ max (max H height) (r+s+n+4); omega
  have hout := responseSink_safe caller P ans kept hz ho
  obtain ⟨k,hk,tr,exec,last,bounds⟩ := record
  have safety (i j) : P ((tr i).data j) := (bounds i j).trans ((le_max_right H height).trans (le_max_left ..))
  have tag : (tr (Fin.last k)).output=some (responseTag ans) := by rw [last]; exact emits_tag emitted
  have invoke := Odd.invoke_memory 2 responseSink P (MinorLog.resume current (words u)).memory caller tr
    (responseTag_lt ans) kept exec safety tag hout
  rw [last] at invoke
  have lastSafe : final.memory.AllData P := by
    intro i
    exact last ▸ safety (Fin.last k) i
  obtain ⟨c,hc,back⟩ := replyBlock_eval P final ans caller emitted lastSafe kept hz ho recv c2 c29
  have bound : prepCost+(2*k+2+c) ≤ serviceClock r s n clock := by unfold serviceClock; omega
  exact ((Fragment.Run.ofBlock prepared).seq (invoke.seq (Fragment.Run.ofBlock back))).mono bound

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
