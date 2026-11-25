import OAI.Optimization.LinearProgramming.BitRAM.Receive

/-! Input loading into the same bit-heap from the ordinary scalar tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

open RAM RAM.Block RAM.Tape OracleSpec

theorem contents_initial_update (p : BitProgram) (input : Word) :
    contents (p.initial input) = Function.update (contents (p.initial [])) (some p.inputStack) input := by
  funext s
  cases s with
  | none => simp [contents,BitProgram.initial]
  | some s =>
    by_cases hs : s=p.inputStack
    · simp [hs,contents,BitProgram.initial]
    · simp [contents,BitProgram.initial,hs]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Bootstrap a frozen program from its actual represented empty initial state. Both packet
base pointers and the full input packet are available to the caller after initialization. -/
theorem loadInput_rep (p : BitProgram) (input : Word) {P : K → Prop} {m : Memory K}
    (rep : Rep p (p.initial []) m) (safe : Good P m) (zero : P 0) (hbase : 3 ≤ m.index recvBaseReg)
    (hlen : m.index recvLenReg=input.length) (packet : ScalarPacket m (m.index recvBaseReg) input) :
    ∃ t, Eval (Good P) (loadChainFromScalars p (some p.inputStack)) m (18*input.length+6) t ∧
      Rep p (p.initial input) t ∧ t.index sendBaseReg=m.index sendBaseReg ∧ t.index recvBaseReg=m.index recvBaseReg ∧
      ScalarPacket t (m.index recvBaseReg) input ∧ ReceiveFrame (some p.inputStack) m t ∧
      t.index freeReg=m.index freeReg+4*input.length := by
  obtain ⟨t,run,heap,frame,free⟩ := loadChainFromScalars_correct (some p.inputStack) input rep.heap safe zero hbase hlen packet
  have preserved (a : Nat) (lo : 37 ≤ a) (hi : a<65) := frame.index a (ReceiveKeep.header rep.heap _ lo hi)
  have next : Rep p (p.initial input) t :=
    ⟨(contents_initial_update p input).symm ▸ heap,(preserved _ (by decide) (by decide)).trans rep.bufferLength,
      (preserved _ (by decide) (by decide)).trans rep.stateCode,(preserved _ (by decide) (by decide)).trans rep.askReady⟩
  exact ⟨t,run,next,preserved _ (by decide) (by decide),preserved _ (by decide) (by decide),
    packet.congr (fun a _ => frame.data _ (by omega) (by omega)),frame,free⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI
