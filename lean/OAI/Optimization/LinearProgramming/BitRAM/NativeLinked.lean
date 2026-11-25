import OAI.Optimization.LinearProgramming.BitRAM.NativeService
import OAI.Optimization.LinearProgramming.BitRAM.FragmentFrame

/-! Link an actual finite numerical RAM query service inside a binary algorithm. The
caller proves the service on the requests reachable in that algorithm; the emitted fragment
executes all the binary control, packet transfers, and physical arithmetic subroutines. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace NativeService
open RAM RAM.Block RAM.Tape RAM.Callable OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure Implements (p : BitProgram) (bo : WordOracle) (handler : Fragment) (P : K→Prop)
    (ctx : Transcript → Memory K → Prop) (allowed : p.Config → Fin p.states → Prop) (rawFactor : Nat) : Prop where
  ports : ∀ h m, ctx h m → 3 ≤ m.index sendBaseReg ∧ 3 ≤ m.index recvBaseReg
  ordinary : ∀ h m t, t.data=m.data → StableHeaders m t → StableEven m t → ctx h m → ctx h t
  writePacket : ∀ c : p.Config, ∀ m t, ctx c.transcript m → PacketWriteEffect m t (m.index sendBaseReg) c.bufferRev → ctx c.transcript t
  readPacket : ∀ h m t, ctx h m → ReceiveReplyFrame p m t → ctx h t
  execute : ∀ c q m, allowed c q → Awaiting p c q m → Good P m → ctx c.transcript m →
    ScalarPacket m (m.index sendBaseReg) c.bufferRev.reverse → ∃ t,
      RawReply handler P m (rawFactor*Dispatch.chargedAsk bo c) (bo c.transcript c.bufferRev.reverse) t ∧
      ctx (Dispatch.answered bo c q).transcript t

def linked (p : BitProgram) (handler : Fragment) : Fragment :=
  Dispatch.fragController p (answer p handler)

/-- Native execution with an actual inlined service, including the scalar bound at
all executed instructions and all previously stored numerical context. -/
theorem run {p : BitProgram} {bo : WordOracle} {handler : Fragment} {P : K→Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop} {rawFactor : Nat}
    (machine : Implements p bo handler P ctx allowed rawFactor) (zero : P 0) (one : P 1)
    {c d : p.Config} {steps : Nat} (source : p.Run bo c steps d) (halt : d.pc=none)
    (valid : Dispatch.PermittedAsksFrom p bo allowed c) {m : Memory K}
    (startRep : Rep p c m) (safe : Good P m) (initial : ctx c.transcript m) :
    ∃ t, (linked p handler).Run P m ((2*p.states+64+rawFactor)*steps+2) t ∧
      Rep p d t ∧ ctx d.transcript t := by
  have handles : Dispatch.FragCallbackCorrect p bo P ctx allowed (answer p handler) (rawFactor+32) :=
    answer_correct p bo handler P ctx allowed rawFactor zero one machine.ports machine.writePacket machine.readPacket machine.execute
  obtain ⟨t,go,rep,last⟩ := Dispatch.fragWithCallback_run_frame handles machine.ordinary source halt valid startRep safe initial
  exact ⟨t,go.mono (by rw [show 2*p.states+32+(rawFactor+32) = 2*p.states+64+rawFactor by omega]),rep,last⟩

/-- Export the chronological bit result of the actual native callback computation to the
public scalar output window. This is the entry point for consumers decoding a typed value. -/
def linkedOutput (p : BitProgram) (handler : Fragment) : Fragment :=
  .seq (linked p handler) (.ofBlock preparePacket)

theorem run_output {p : BitProgram} {bo : WordOracle} {handler : Fragment} {P : K→Prop}
    {ctx : Transcript → Memory K → Prop} {allowed : p.Config → Fin p.states → Prop} {f : Nat}
    (machine : Implements p bo handler P ctx allowed f) (zero : P 0) (one : P 1)
    {c d : p.Config} {steps : Nat} (source : p.Run bo c steps d) (halt : d.pc=none)
    (valid : Dispatch.PermittedAsksFrom p bo allowed c) {m : Memory K}
    (startRep : Rep p c m) (safe : Good P m) (initial : ctx c.transcript m) :
    ∃ t, (linkedOutput p handler).Run P m (((2*p.states+64+f)*steps+2)+(13*d.bufferRev.length+7)) t ∧
      Rep p d t ∧ ctx d.transcript t ∧ t.index bufferLenReg=d.bufferRev.reverse.length ∧
      ScalarPacket t (t.index sendBaseReg) d.bufferRev.reverse := by
  obtain ⟨b,go,rep,env⟩ := run machine zero one source halt valid startRep safe initial
  obtain ⟨t,emit,rt,ef⟩ := preparePacket_correct rep go.safe_end zero one (machine.ports _ _ env).1
  refine ⟨t,go.seq (Fragment.Run.ofBlock emit),rt,machine.writePacket d b t env ef,?_,?_⟩
  · simpa using rt.bufferLength
  · rw [ef.index _ (by decide)]; exact ef.packet

end NativeService
end BitRAM
end LinearProgramming
end Optimization
end OAI
