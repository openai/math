import OAI.Optimization.LinearProgramming.BitRAM.HeapPush
import OAI.Optimization.LinearProgramming.BitRAM.HeapAccess
import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout

/-! An actual incoming scalar bit becomes one immutable node in the linked binary stack. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM RAM.Block RAM.Tape OracleSpec

/-- All addresses in the existing heap other than the chosen head and allocator survive;
every even register outside the documented three working registers survives as well. -/
def ReceiveKeep {p : BitProgram} (slot : Slot p) (m : Memory K) (i : Nat) : Prop :=
  i ≠ 0 ∧ i ≠ 10 ∧ i ≠ 12 ∧ i ≠ freeReg ∧ i ≠ headReg slot ∧ (i < m.index freeReg ∨ i%2=0)

structure ReceiveFrame {p : BitProgram} (slot : Slot p) (m t : Memory K) : Prop where
  data (a : Nat) (h0 : a ≠ 0) (h2 : a ≠ 2) : t.data a=m.data a
  index (a : Nat) (h : ReceiveKeep slot m a) : t.index a=m.index a

theorem ReceiveKeep.mono {p : BitProgram} {s : Slot p} {m t : Memory K} {i : Nat}
    (h : ReceiveKeep s m i) (grows : m.index freeReg ≤ t.index freeReg) : ReceiveKeep s t i := by
  rcases h with ⟨h0,h10,h12,hf,hhead,below|even⟩
  · exact ⟨h0,h10,h12,hf,hhead,Or.inl (below.trans_le grows)⟩
  · exact ⟨h0,h10,h12,hf,hhead,Or.inr even⟩

theorem ReceiveKeep.header {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    (s : Slot p) {i : Nat} (lo : 37 ≤ i) (hi : i < 65) : ReceiveKeep s m i := by
  have hfree := h.freeLower
  have hb : 65 ≤ heapStart p := by unfold heapStart; omega
  refine ⟨by omega,by omega,by omega,by unfold freeReg; omega,?_,Or.inl (by omega)⟩
  cases s with
  | none => change i ≠ 35; omega
  | some a => change i ≠ 65+2*a.val; omega

theorem ReceiveFrame.trans {p : BitProgram} {s : Slot p} {m u t : Memory K}
    (first : ReceiveFrame s m u) (rest : ReceiveFrame s u t) (growth : m.index freeReg ≤ u.index freeReg) :
    ReceiveFrame s m t := ⟨fun i h0 h2 => (rest.data i h0 h2).trans (first.data i h0 h2),
      fun i hi => (rest.index i (hi.mono growth)).trans (first.index i hi)⟩

def receivePush {p : BitProgram} (s : Slot p) : Block :=
  .branch (.scalarLT 0 2) (push (headReg s) true) (.seq (.op (.addrConst 0 0)) (push (headReg s) false))

def receiveBody {p : BitProgram} (s : Slot p) : Block :=
  .seq (.op (.decr 12 12)) (.seq (.op (.load 2 12)) (receivePush s))

def receiveLoop {p : BitProgram} (s : Slot p) : Block := .loop (.addrLT recvBaseReg 12) (receiveBody s)

private structure BitPushFrame (m t : Memory K) (head : Nat) : Prop where
  data : t.data=m.data
  frontier : t.index freeReg=m.index freeReg+4
  index (i : Nat) : i ≠ 0 → i ≠ freeReg → i ≠ head → i ≠ m.index freeReg → i ≠ m.index freeReg+2 → t.index i=m.index i

private theorem BitPushFrame.of_effect {m u t : Memory K} {head : Nat} {b : Bool}
    (hd : u.data=m.data) (hi : ∀ i, i ≠ 0 → u.index i=m.index i) (h : PushEffect u t head b) :
    BitPushFrame m t head := by
  have hf := hi freeReg (by decide)
  refine ⟨h.data.trans hd,by rw [h.frontier,hf],?_⟩
  intro i i0 ifr ih i1 i2
  exact (h.frame i ifr ih (by simpa only [hf] using i1) (by simpa only [hf] using i2)).trans (hi i i0)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem receivePush_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (hm : Good P m) (s : Slot p) (b : Bool) (hz : m.data 0=0) (hbit : m.data 2=bitScalar b) :
    ∃ t, Eval (Good P) (receivePush s) m 10 t ∧ BitPushFrame m t (headReg s) ∧
      HeapRep p (Function.update w s (b::w s)) t := by
  cases b with
  | false =>
    let u := m.putIndex 0 0
    have pre : Eval (Good P) (.op (.addrConst 0 0)) m 1 u := Eval.op_addrConst m 0 0 hm hm
    obtain ⟨t,run,eff,rep⟩ := push_correct (h.putScratch (i:=0) (by decide) 0) pre.safe_end s false
    have frame : BitPushFrame m t (headReg s) := .of_effect (u := u.putIndex 0 (bitNat false)) rfl (fun i hi => by simp [u,hi]) eff
    refine ⟨t,?_,frame,rep⟩
    apply Eval.branchFalse (c:=.scalarLT 0 2) _ (pre.seq run)
    simp [Cond.test,hz,hbit,bitScalar]
  | true =>
    obtain ⟨t,run,eff,rep⟩ := push_correct h hm s true
    have frame : BitPushFrame m t (headReg s) := .of_effect (u := m.putIndex 0 (bitNat true)) rfl (fun i hi => by simp [hi]) eff
    refine ⟨t,?_,frame,rep⟩
    apply Eval.branchTrue (c:=.scalarLT 0 2) _ run
    simp [Cond.test,hz,hbit,bitScalar]

structure ReceiveBitStep {p : BitProgram} (s : Slot p) (m t : Memory K) : Prop where
  data (a : Nat) (h : a ≠ 2) : t.data a=m.data a
  frontier : t.index freeReg=m.index freeReg+4
  cursor : t.index 12=m.index 12-1
  frame : ReceiveFrame s m t

/-- One reverse cursor decrement, one indirect scalar read, one comparison and one linked
node allocation. Both bit values take exactly 12 instructions. -/
theorem receiveBody_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (hm : Good P m) (s : Slot p) (b : Bool) (hz : m.data 0=0)
    (hbit : m.data (m.index 12-1)=bitScalar b) :
    ∃ t, Eval (Good P) (receiveBody s) m 12 t ∧ ReceiveBitStep s m t ∧
      HeapRep p (Function.update w s (b::w s)) t := by
  let u := m.putIndex 12 (m.index 12-1)
  let v := u.putData 2 (u.data (u.index 12))
  have eu : Eval (Good P) (.op (.decr 12 12)) m 1 u := Eval.op_decr m 12 12 hm hm
  have hv : Good P v := fun a => by
    by_cases ha : a=2
    · simpa [v,ha] using eu.safe_end (u.index 12)
    · simpa [v,u,ha] using hm a
  have ev : Eval (Good P) (.op (.load 2 12)) u 1 v := Eval.op_load u 2 12 hm hv
  have heap : HeapRep p w v := (h.putScratch (i:=12) (by decide) _).of_odd_eq (fun _ _ _ => rfl)
  have vz : v.data 0=0 := by simpa [v,u] using hz
  have vb : v.data 2=bitScalar b := by simpa [v,u] using hbit
  obtain ⟨t,ep,ef,rep⟩ := receivePush_correct heap hv s b vz vb
  have fr : v.index freeReg=m.index freeReg := by simp [v,u,freeReg]
  have low : 65 ≤ m.index freeReg := (show 65 ≤ heapStart p by unfold heapStart; omega).trans h.freeLower
  have odd := h.freeOdd
  have range := headReg_range p s
  have hd (a : Nat) (ha : a ≠ 2) : t.data a=m.data a := by rw [ef.data]; simp [v,u,ha]
  refine ⟨t,eu.seq (ev.seq ep),⟨hd,ef.frontier.trans (by rw [fr]),?_,⟨fun i _ h2 => hd i h2,?_⟩⟩,rep⟩
  · rw [ef.index 12 (by decide) (by decide) (by omega) (by rw [fr]; omega) (by rw [fr]; omega)]
    simp [v,u]
  · intro i hi
    rcases hi with ⟨h0,_,h12,hfree,hhead,hpos⟩
    rw [ef.index i h0 hfree hhead (by rw [fr]; omega) (by rw [fr]; omega)]
    simp [v,u,h12]

end BitRAM
end LinearProgramming
end Optimization
end OAI
