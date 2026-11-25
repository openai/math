import OAI.Optimization.LinearProgramming.Compression.SignWireReusable
import OAI.Optimization.LinearProgramming.Compression.SignWireProtocol
import OAI.Optimization.LinearProgramming.BitRAM.NativeLinked

/-! Linked BitRAM implementation of the lattice's canonical sign-word oracle,
including a transcript-indexed persistent numerical cache and a uniform
per-request charge. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache OracleSpec
open scoped BigOperators

def CallbackContext (n fuel prec B C firstR cap src base send recv : ℕ)
    (mag : ℕ → ℚ) (L : Buffers) (hist : Transcript) (m : Memory ℚ) : Prop :=
  PublicPorts (n+1) send recv src base m ∧
    ResidentHigh (n:=n) mag L fuel prec C (firstR+hist.length*(cachedProxySignSteps n fuel C+5))
      cap base (fun q => ratBits q ≤ wordComparatorBits n fuel prec B) m

/-- The ordinary finite RAM handler implements the three-way mathematical
oracle for any bit program whose reachable requests have the stated form.
Its persistent arena survives every ordinary instruction and both physical
packet transfers. Repeated invocations have an additive address bound. -/
theorem wordComparator_implements (p : BitProgram) (n fuel prec B C firstR calls cap src base send recv : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (bits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (cut : (2:ℤ)^prec*A ≤ 2^fuel) (hcap : symbolicQueryCap n fuel ≤ C)
    (hstart : C ≤ firstR)
    (hcode : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ firstR)
    (window : 2*(firstR+calls*(cachedProxySignSteps n fuel C+5))+1 ≤ cap)
    (arena : CallbackArena n fuel cap base src send recv) :
    BitRAM.NativeService.Implements p (cachedWordOracle n fuel prec mag) wordComparator
      (fun q => ratBits q ≤ wordComparatorBits n fuel prec B)
      (CallbackContext n fuel prec B C firstR cap src base send recv mag L)
      (AllowedSignPacket n calls A p) (wordComparatorTime n fuel C) := by
  let P := fun q : ℚ => ratBits q ≤ wordComparatorBits n fuel prec B
  let S := cachedProxySignSteps n fuel C+5
  constructor
  · rintro hist m ⟨ports,_⟩
    change 3 ≤ m.index 43 ∧ 3 ≤ m.index 47
    rw [ports.query,ports.answer]
    have := arena.rowHeader;have := arena.sendOutside;have := arena.replyOutside
    omega
  · rintro hist m t data headers evens ⟨ports,mem⟩
    exact ⟨ports.headers headers,mem.ofFrame data evens⟩
  · rintro cfg m t ⟨ports,mem⟩ wrote
    exact ⟨ports.transfer (fun i h => wrote.index i (by omega)),mem.packetWrite wrote
      (by rw [ports.query];exact arena.sendOutside)⟩
  · rintro hist m t ⟨ports,mem⟩ rr
    exact ⟨ports.headers rr.headers,mem.receiveReply rr⟩
  · intro cfg q m permit waiting hsafe ctx packet
    obtain ⟨callsLeft,row,packetEq,budget⟩ := permit
    obtain ⟨ports,mem⟩ := ctx
    let R := firstR+cfg.transcript.length*S
    let addr := max (2*C) (2*R+1)
    have enough : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr := by
      have hR : firstR ≤ R := Nat.le_add_right ..
      exact (show _ ≤ 2*R+1 by omega).trans (le_max_right ..)
    have room : addr+(cachedProxySignSteps n fuel C+5) ≤ cap :=
      (cap_for_resident_steps firstR S C calls cfg.transcript.length hstart callsLeft).trans window
    have length : m.index 37=(Lattice.signRowWord row).length := by
      rw [← packetEq,List.length_reverse]
      exact waiting.bufferLength
    have sent : BitRAM.ScalarPacket m send (Lattice.signRowWord row) := by
      change BitRAM.ScalarPacket m (m.index 43) cfg.bufferRev.reverse at packet
      simpa only [ports.query,packetEq] using packet
    obtain ⟨t,reply,ps,cache⟩ := wordComparator_reusable fuel prec B C R addr cap src base send recv A mag
      L m row bits budget cut hcap enough le_rfl room arena ports hsafe mem length sent
    have result : cachedWordOracle n fuel prec mag cfg.transcript cfg.bufferRev.reverse =
        Lattice.signReply (formOrdering (DyadicRAM.cachedForm fuel prec mag row)) := by
      rw [packetEq];exact Lattice.wordSignOracle_query _ _ _
    have limit : 1 ≤ BitRAM.Dispatch.chargedAsk (cachedWordOracle n fuel prec mag) cfg := by
      unfold BitRAM.Dispatch.chargedAsk;omega
    have clock : wordComparatorTime n fuel C ≤
        wordComparatorTime n fuel C*BitRAM.Dispatch.chargedAsk (cachedWordOracle n fuel prec mag) cfg :=
      Nat.le_mul_of_pos_right _ limit
    have next : nextResidentBound n fuel C R=firstR+(cfg.transcript.length+1)*S :=
      nextResidentBound_step n fuel C firstR cfg.transcript.length hstart hcode
    refine ⟨t,?_,ps,?_⟩
    · rw [result]
      exact ⟨reply.run.mono clock,reply.packet,reply.length,reply.frame⟩
    · have newLength : (BitRAM.Dispatch.answered (cachedWordOracle n fuel prec mag) cfg q).transcript.length =
          cfg.transcript.length+1 := rfl
      change ResidentHigh (n:=n) mag L fuel prec C
        (firstR+(BitRAM.Dispatch.answered (cachedWordOracle n fuel prec mag) cfg q).transcript.length*S) cap base P t
      rw [newLength,← next]
      exact cache

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
