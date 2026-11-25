import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout
import OAI.Optimization.LinearProgramming.RAM.CallableControl

/-! Calling convention of a finite native RAM program answering a serialized binary query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace NativeService
open RAM RAM.Tape OracleSpec RAM.Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A real instruction fragment, the actual binary reply cells and length, and the
protected odd addresses. A callee may choose its response base at runtime. -/
structure RawReply (handler : Fragment) (P : K → Prop) (m : Memory K) (limit : Nat)
    (reply : Word) (t : Memory K) : Prop where
  run : handler.Run P m limit t
  packet : ScalarPacket t (t.index recvBaseReg) reply
  length : t.index recvLenReg=reply.length
  frame : ∀ i, 31 ≤ i → i%2=1 → i≠recvBaseReg → i≠recvLenReg → t.index i=m.index i

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- A returning native handler preserves every live immutable stack. -/
theorem heap_of_frame {p : BitProgram} {w : Slot p → Word} {m t : Memory K}
    (frame : ∀ i, 31 ≤ i → i%2=1 → i≠recvBaseReg → i≠recvLenReg → t.index i=m.index i)
    (h : HeapRep p w m) : HeapRep p w t := by
  apply ((h.putOther recvBaseReg (t.index recvBaseReg) (by unfold recvBaseReg heapStart; omega)
    (by decide) (by decide) (by
      intro s; cases s with
      | none => change 47 ≠ 35; decide
      | some i => change 47 ≠ 65+2*i.val; omega)).putOther recvLenReg (t.index recvLenReg)
    (by unfold recvLenReg heapStart; omega) (by decide) (by decide) (by
      intro s; cases s with
      | none => change 49 ≠ 35; decide
      | some i => change 49 ≠ 65+2*i.val; omega)).of_odd_eq
  intro i low odd
  by_cases hl : i=recvLenReg
  · subst i; simp
  · by_cases hb : i=recvBaseReg
    · subst i; simp [hl]
    · simp only [Memory.putIndex_ne _ hl,Memory.putIndex_ne _ hb]
      exact frame i low odd hb hl

theorem RawReply.heap {p : BitProgram} {w : Slot p → Word} {handler : Fragment} {P : K → Prop}
    {m t : Memory K} {limit : Nat} {bits : Word} (r : RawReply handler P m limit bits t)
    (h : HeapRep p w m) : HeapRep p w t := heap_of_frame r.frame h

end NativeService
end BitRAM
end LinearProgramming
end Optimization
end OAI
