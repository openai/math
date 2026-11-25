import OAI.Optimization.LinearProgramming.BitRAM.Ops
import OAI.Optimization.LinearProgramming.BitRAM.Boot
import OAI.Optimization.LinearProgramming.BitRAM.ReceiveInput

/-! Call a finite compiled bit program in the middle of a numerical RAM computation.
The request, receive, and input windows are supplied in physical address registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
open RAM RAM.Block RAM.Tape OracleSpec

private theorem below_heads (p : BitProgram) {i : Nat} (low : i<65) : i∉headKeys p := by
  intro h
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp h
  change 65+2*s.val<65 at low
  omega

def configuredEntry (p : BitProgram) : Block := .seq (reset p) (loadChainFromScalars p (some p.inputStack))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem configuredEntry_complete_frame (p : BitProgram) (w : Word) (m : Memory K) {P : K → Prop}
    (safe : Good P m) (zero : P 0) (base : 3 ≤ m.index recvBaseReg) (len : m.index recvLenReg=w.length)
    (packet : ScalarPacket m (m.index recvBaseReg) w) :
    ∃ t, Eval (Good P) (configuredEntry p) m (18*w.length+p.stackCount+12) t ∧ Rep p (p.initial w) t ∧
      (∀ i, 43 ≤ i → i<65 → t.index i=m.index i) ∧
      (∀ i, i ≠ 0 → i ≠ 2 → t.data i=m.data i) ∧ StableEven m t := by
  obtain ⟨a,clear,empty,ad,idx⟩ := reset_correct p m safe
  have kept (i : Nat) (low : 43 ≤ i) (high : i<65) : a.index i=m.index i := by
    apply idx i _ (below_heads p high)
    simp [nilReg,freeReg,bufferReg,bufferLenReg,stateReg,askReg]
    omega
  have ab := kept recvBaseReg (by decide) (by decide)
  have aw := (kept recvLenReg (by decide) (by decide)).trans len
  have ap : ScalarPacket a (a.index recvBaseReg) w := by rw [ab]; exact packet.congr (fun _ _ => congrFun ad _)
  obtain ⟨t,read,rep,_,_,_,fr,_⟩ := loadInput_rep p w empty clear.safe_end zero (by omega) aw ap
  refine ⟨t,?_,rep,?_,fun i h0 h2 => (fr.data i h0 h2).trans (congrFun ad i),?_⟩
  · rw [show 18*w.length+p.stackCount+12=(6+p.stackCount)+(18*w.length+6) by omega]
    exact clear.seq read
  · intro i low high
    exact (fr.index i (ReceiveKeep.header empty.heap (some p.inputStack) (by omega) high)).trans (kept i low high)

  · intro i lower even
    have headOdd := (headReg_range p (some p.inputStack)).2.2
    have keptBefore : a.index i=m.index i := by
      apply idx i
      · simp [nilReg,freeReg,bufferReg,bufferLenReg,stateReg,askReg]
        omega
      · intro mem
        obtain ⟨s,_,rfl⟩ := List.mem_map.mp mem
        have := (headReg_range p (some s)).2.2
        omega
    exact (fr.index i ⟨by omega,by omega,by omega,by unfold freeReg; omega,by omega,Or.inr even⟩).trans keptBefore

theorem configuredEntry_correct (p : BitProgram) (w : Word) (m : Memory K) {P : K → Prop}
    (safe : Good P m) (zero : P 0) (base : 3 ≤ m.index recvBaseReg) (len : m.index recvLenReg=w.length)
    (packet : ScalarPacket m (m.index recvBaseReg) w) :
    ∃ t, Eval (Good P) (configuredEntry p) m (18*w.length+p.stackCount+12) t ∧ Rep p (p.initial w) t ∧
      (∀ i, 43 ≤ i → i<65 → t.index i=m.index i) ∧ ∀ i, i ≠ 0 → i ≠ 2 → t.data i=m.data i := by
  obtain ⟨t,run,rep,headers,data,_⟩ := configuredEntry_complete_frame p w m safe zero base len packet
  exact ⟨t,run,rep,headers,data⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI
