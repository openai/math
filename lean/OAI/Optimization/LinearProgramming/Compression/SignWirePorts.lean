import OAI.Optimization.LinearProgramming.Compression.SignWireRepeat
import OAI.Optimization.LinearProgramming.Compression.SignWireShellFrames
import OAI.Optimization.LinearProgramming.BitRAM.NativeService

/-! Public callback ports and the finite numerical cache remain available
during packet reads, replies, and ordinary bit-machine transitions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache

theorem NumericReceipt.oddIndex {n fuel prec C R cap src base : ℕ} {P : ℚ → Prop}
    {mag : ℕ → ℚ} {L : Buffers} {m t : Memory ℚ} {row : Fin (n+1) → ℤ}
    (h : NumericReceipt mag L fuel prec C R cap src base P row m t) (i : ℕ) (odd : i%2=1) :
    t.index i=m.index i := by
  obtain ⟨stage,old,logical,last,work,st,_,_,_,_,_,_,_,endState⟩ := h
  obtain ⟨j,rfl⟩ : ∃ j, i=2*j+1 := ⟨i/2,by omega⟩
  rw [endState,Memory.putIndex_ne _ (by omega),Call.index_odd]
  exact st.odd (2*j+1) odd

theorem ResidentHigh.transferWindow {n fuel prec C R cap base : ℕ}
    {mag : ℕ → ℚ} {L : Buffers} {P : ℚ → Prop} {m t : Memory ℚ}
    (h : ResidentHigh (n:=n) mag L fuel prec C R cap base P m)
    (d : ∀ i, 32 ≤ i → i ≤ cap → t.data (2*i)=m.data (2*i))
    (ix : BitRAM.StableEven m t) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  obtain ⟨old,caller,res,shell⟩ := h
  exact ⟨old,caller,res,shell.transfer (fun i hi hc _ => d i hi hc)
    (fun i hi => ix (2*i) (by omega) (by omega))⟩

theorem WireReadFrame.resident {n fuel prec C R cap src base : ℕ}
    {mag : ℕ → ℚ} {L : Buffers} {P : ℚ → Prop} {m t : Memory ℚ}
    (read : WireReadFrame m t src (n+1)) (far : 2*cap < src)
    (env : ResidentHigh (n:=n) mag L fuel prec C R cap base P m) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  obtain ⟨old,caller,num,shell⟩ := env
  exact ⟨old,caller,num,read.highShell far shell⟩

theorem ReplyWriteFrame.resident {n fuel prec C R cap base : ℕ}
    {mag : ℕ → ℚ} {L : Buffers} {P : ℚ → Prop} {m t : Memory ℚ}
    (write : ReplyWriteFrame m t) (far : 2*cap < m.index 47)
    (env : ResidentHigh (n:=n) mag L fuel prec C R cap base P m) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  obtain ⟨old,caller,num,shell⟩ := env
  exact ⟨old,caller,num,write.highShell far shell⟩

theorem ResidentHigh.packetWrite {n fuel prec C R cap base : ℕ}
    {mag : ℕ → ℚ} {L : Buffers} {P : ℚ → Prop} {m t : Memory ℚ} {bits : OracleSpec.Word}
    (h : ResidentHigh (n:=n) mag L fuel prec C R cap base P m)
    (wrote : BitRAM.PacketWriteEffect m t (m.index 43) bits) (far : 2*cap < m.index 43) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t := by
  apply h.transferWindow
  · intro j hi hc;exact wrote.data (2*j) (by omega) (Or.inl (by omega))
  · intro i hi _;exact wrote.index i (by omega)

theorem ResidentHigh.receiveReply {n fuel prec C R cap base : ℕ}
    {mag : ℕ → ℚ} {L : Buffers} {P : ℚ → Prop} {m t : Memory ℚ} {p : OracleSpec.BitProgram}
    (h : ResidentHigh (n:=n) mag L fuel prec C R cap base P m) (rr : BitRAM.ReceiveReplyFrame p m t) :
    ResidentHigh (n:=n) mag L fuel prec C R cap base P t :=
  h.transferWindow (fun j hi _ => rr.data (2*j) (by omega) (by omega)) rr.even

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
