import OAI.Optimization.LinearProgramming.BitRAM.ServiceRaw
import OAI.Optimization.LinearProgramming.BitRAM.DispatchSource
import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.BitRAM.PacketWrite
import OAI.Optimization.LinearProgramming.BitRAM.ReceiveReply

/-! The bitcode can call a native comparison routine with arbitrary relocated RAM
subprograms. The compiled instructions transfer its query and answer through real cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace NativeService
open RAM RAM.Block RAM.Tape RAM.Callable OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def answer (p : BitProgram) (handler : Fragment) : Fragment :=
  .seq (.ofBlock preparePacket) (.seq handler (.ofBlock (receiveReply p)))

/-- Supply a native handler on the serialized packets allowed by the source computation.
The numerical application state in `ctx` may depend on the source history. -/
theorem answer_correct (p : BitProgram) (bo : WordOracle) (handler : Fragment)
    (P : K→Prop) (ctx : Transcript → Memory K → Prop) (allowed : p.Config → Fin p.states → Prop)
    (rawFactor : Nat) (zero : P 0) (one : P 1)
    (ports : ∀ hist m, ctx hist m → 3≤m.index sendBaseReg ∧ 3≤m.index recvBaseReg)
    (written : ∀ c : p.Config, ∀ m t, ctx c.transcript m →
      PacketWriteEffect m t (m.index sendBaseReg) c.bufferRev → ctx c.transcript t)
    (readBack : ∀ hist m t, ctx hist m → ReceiveReplyFrame p m t → ctx hist t)
    (raw : ∀ c q m, allowed c q → Awaiting p c q m → Good P m → ctx c.transcript m →
      ScalarPacket m (m.index sendBaseReg) c.bufferRev.reverse → ∃ t,
        RawReply handler P m (rawFactor*Dispatch.chargedAsk bo c) (bo c.transcript c.bufferRev.reverse) t ∧
        ctx (Dispatch.answered bo c q).transcript t)
    (c : p.Config) (q : Fin p.states) (m : Memory K) (permitted : allowed c q)
    (wait : Awaiting p c q m) (safe : Good P m) (hc : ctx c.transcript m) :
    ∃ t, (answer p handler).Run P m ((rawFactor+32)*Dispatch.chargedAsk bo c) t ∧
      Rep p (Dispatch.answered bo c q) t ∧ ctx (Dispatch.answered bo c q).transcript t := by
  let packet := c.bufferRev.reverse
  let ans := bo c.transcript packet
  obtain ⟨u,prep,heap,out⟩ := preparePacket_heap_correct wait.heap safe zero one (ports _ _ hc).1 wait.bufferLength
  have up : Awaiting p c q u := ⟨heap,(out.index _ (by decide)).trans wait.bufferLength,
    (out.index _ (by decide)).trans wait.stateCode,(out.index _ (by decide)).trans wait.askFlag⟩
  have hpack : ScalarPacket u (u.index sendBaseReg) packet := by rw [out.index _ (by decide)]; exact out.packet
  obtain ⟨v,response,vctx⟩ := raw c q u permitted up prep.safe_end (written c m u hc out) hpack
  have st : v.index stateReg=q.val := (response.frame _ (by decide) (by decide) (by decide) (by decide)).trans up.stateCode
  obtain ⟨t,read,rep,rf,_⟩ := receiveReply_rep_bits p c q ans (response.heap heap) response.run.safe_end
    zero st (ports _ _ vctx).2 response.length response.packet
  refine ⟨t,((Fragment.Run.ofBlock prep).seq (response.run.seq (Fragment.Run.ofBlock read))).mono ?_,rep,readBack _ _ _ vctx rf⟩
  change 13*c.bufferRev.length+7+(rawFactor*Dispatch.chargedAsk bo c+(18*ans.length+9)) ≤ (rawFactor+32)*Dispatch.chargedAsk bo c
  rw [Nat.add_mul]
  simp only [Dispatch.chargedAsk,List.length_reverse,ans,packet]
  omega

end NativeService
end BitRAM
end LinearProgramming
end Optimization
end OAI
