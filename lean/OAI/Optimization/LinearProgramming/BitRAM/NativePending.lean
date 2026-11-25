import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.BitRAM.PacketWrite

/-! The suspended bit instruction's chronological request and program state coexist
at the actual numerical callback entry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
open RAM RAM.Block RAM.Tape OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem prepare_awaiting {p : BitProgram} {c : p.Config} {q : Fin p.states} {m : Memory K}
    {P : K→Prop} (pending : Awaiting p c q m) (safe : Good P m) (zero : P 0) (one : P 1)
    (base : 3 ≤ m.index sendBaseReg) :
    ∃ u, Eval (Good P) preparePacket m (13*c.bufferRev.length+7) u ∧ Awaiting p c q u ∧
      PacketWriteEffect m u (m.index sendBaseReg) c.bufferRev ∧
      ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse := by
  obtain ⟨u,emit,heap,effect⟩ := preparePacket_heap_correct pending.heap safe zero one base pending.bufferLength
  refine ⟨u,emit,⟨heap,(effect.index _ (by decide)).trans pending.bufferLength,
    (effect.index _ (by decide)).trans pending.stateCode,(effect.index _ (by decide)).trans pending.askFlag⟩,effect,?_⟩
  rw [effect.index _ (by decide)]
  exact effect.packet

end BitRAM
end LinearProgramming
end Optimization
end OAI
