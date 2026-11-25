import OAI.Optimization.LinearProgramming.Recovery.PriceResponse
import OAI.Optimization.LinearProgramming.Recovery.EpochSetup

/-! Run the actual price handler at a suspended finite learner. A native interruption
returns without deserialization. A successful call consumes exactly its computed bit. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM RAM.Callable OracleSpec Contract BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

theorem Stored.safe {S : Service D E} {x : LabelInput.Buffers r s n} {h : History ℚ} {H W : ℕ}
    {a : Memory ℚ} (stored : Stored S x h H a) (height : S.height ≤ H) (room : H ≤ W)
    (ready : RowRAM.Within S.height S.ready.memory) : a.AllData (fun z=>ratBits z ≤ W) := by
  obtain ⟨minor,g,rfl,trained,_,gs,_⟩:=stored
  exact Odd.allData _ _ (cache_safe S trained ready (height.trans room)) (fun j=>(gs j).trans room)

theorem preservedPorts_trans {a b c : Memory ℚ} (ab : preservedPorts a b) (bc : preservedPorts b c) : preservedPorts a c :=
  ⟨bc.1.trans ab.1,fun j lo hi=>(bc.2 j lo hi).trans (ab.2 j lo hi)⟩

theorem Ports.of_preserved {anchor : Fin n} {base : ℕ} {m t : Memory ℚ} (h : Ports anchor base m)
    (fr : preservedPorts m t) : Ports anchor base t :=
  ⟨fr.1.symm ▸ h.send,(fr.2 _ (by decide) (by decide)).trans h.columns,(fr.2 _ (by decide) (by decide)).trans h.index,
    (fr.2 _ (by decide) (by decide)).trans h.packet⟩

private theorem receive_ports {p : BitProgram} {w : Slot p→Word} {v t : Memory ℚ} (h : HeapRep p w v)
    (frame : ReceiveReplyFrame p v t) : preservedPorts v t := by
  have keep (i : ℕ) (lo : 43 ≤ i) (hi : i < 65) : t.index i=v.index i := by
    exact frame.index i (ReceiveKeep.header h _ (by omega) hi) (by unfold bufferReg;omega) (by unfold bufferLenReg;omega) (by unfold askReg;omega)
  exact ⟨keep _ (by decide) (by decide),fun i lo hi=>keep i (by omega) hi⟩

def transferTime (r s n serviceCost L : ℕ) := 4*(13*L+7)+priceHandlerTime r s n serviceCost L+4*(18+9)+2

theorem transferTime_mono (r s n cost : ℕ) {a b : ℕ} (h : a ≤ b) : transferTime r s n cost a ≤ transferTime r s n cost b := by
  unfold transferTime priceHandlerTime numericPriceTime NativePrice.packetTime
  gcongr

def TrialResult (p : BitProgram) (c : p.Config) (q : Fin p.states) (v : Memory ℚ) : Option Bool→Prop
  | none => v.index nilReg=0 ∧ v.index statusReg=1
  | some b => Rep p (receivedConfig p c q [b]) v ∧ v.index statusReg=0

theorem transfer_at_price (S : Service D E) (x : LabelInput.Buffers r s n) (q : PriceGame.Query n)
    (old : History ℚ) {p : BitProgram} {c : p.Config} {pc : Fin p.states} (native vm : Memory ℚ)
    (wait : Awaiting p c pc vm) (clean : vm.index statusReg=0) (word : c.bufferRev.reverse=priceQuery q.index q.prices)
    (send : 3 ≤ vm.index sendBaseReg) (room : 256+(priceQuery q.index q.prices).length ≤ x.dual)
    (H e W : ℕ) (stored : Stored S x old H native) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n)
    (vmSafe : vm.AllData (fun z=>ratBits z ≤ W)) (all : H+geometricIncrement r s n e S.outputBits ≤ W)
    (arg : (priceQuery q.index q.prices).length+3 ≤ H) (encoded : (priceQuery q.index q.prices).length+3 ≤ e)
    (matrix : ∀i j,ratBits (D i j) ≤ e) (height : S.height ≤ H) (ready : RowRAM.Within S.height S.ready.memory) :
    ∃ next v,(transfer p (priceHandler S.program)).Run (fun z=>ratBits z ≤ W) (Odd.memory native vm)
      (transferTime r s n S.clock (priceQuery q.index q.prices).length) (Odd.memory next v) ∧
      Stored S x (S.priceStep old q).2 (H+geometricIncrement r s n e S.outputBits) next ∧
      TrialResult p c pc v (S.priceStep old q).1 ∧ preservedPorts vm v := by
  let L:=(priceQuery q.index q.prices).length
  let allowance:=priceHandlerTime r s n S.clock L
  let fresh:=Stored S x (S.priceStep old q).2 (H+geometricIncrement r s n e S.outputBits)
  have Hle : H ≤ W := (Nat.le_add_right H _).trans all
  have safe:=stored.safe height Hle ready
  have vals:=NativePrice.values_packet q.index q.prices W (arg.trans Hle)
  have hz : ratBits (0:ℚ) ≤ W:=by simpa using vals.counter 0 (by omega)
  have ho : ratBits (1:ℚ) ≤ W:=by simpa using vals.counter 1 (by omega)
  have length : c.bufferRev.length=L := by simpa [L] using congrArg List.length word
  have invoke (u : Memory ℚ) (pending : Awaiting p c pc u) (us : u.AllData (fun z=>ratBits z ≤ W))
      (eff : PacketWriteEffect vm u (vm.index sendBaseReg) c.bufferRev) (pkt : ScalarPacket u (u.index sendBaseReg) c.bufferRev.reverse) :
      ∃ a v,(priceHandler S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory native u) allowance (Odd.memory a v) ∧
        fresh a ∧ Response p c pc u v (S.priceStep old q).1 ∧ preservedPorts vm u := by
    have readySend : 3 ≤ u.index 43 := (eff.index sendBaseReg (by decide)).symm ▸ send
    obtain ⟨a,v,run,cache',response⟩:=handler_at_price S x q old native u pending ((eff.index statusReg (by decide)).trans clean)
      (word ▸ pkt) (pending.bufferLength.trans length) readySend room H e W stored hD hrn us all arg encoded matrix height ready
    exact ⟨a,v,run,cache',response,eff.index sendBaseReg (by decide),fun i hi _=>eff.index i (by omega)⟩
  cases tag : (S.priceStep old q).1 with
  | none =>
    let saved (a v : Memory ℚ):=fresh a ∧ v.index nilReg=0 ∧ v.index statusReg=1 ∧ preservedPorts vm v
    obtain ⟨a,v,run,_,kept,nil0,flag,ports⟩:=transfer_restart (P := fun z : ℚ => ratBits z ≤ W) wait vmSafe safe hz ho send (priceHandler S.program) allowance saved (by
      intro u pending us eff pkt
      obtain ⟨a,v,real,keep,response,pre⟩:=invoke u pending us eff pkt
      rw [tag] at response
      obtain ⟨nil0,flag,frame⟩:=response
      exact ⟨a,v,real,by omega,keep,nil0,flag,preservedPorts_trans pre frame⟩)
    refine ⟨a,v,run.mono ?_,kept,⟨nil0,flag⟩,ports⟩
    change 4*(13*c.bufferRev.length+7)+allowance+2 ≤ transferTime r s n S.clock L
    rw [length];unfold transferTime allowance;omega
  | some b =>
    let saved (a v : Memory ℚ):=fresh a ∧ preservedPorts vm v ∧ HeapRep p (contents c) v
    obtain ⟨a,v,t,run,rep,normal,⟨keep,ports,heap⟩,frame⟩:=transfer_answer (P := fun z : ℚ => ratBits z ≤ W) wait vmSafe safe hz ho send (priceHandler S.program) allowance [b] saved (by
      intro u pending us eff pkt
      obtain ⟨a,v,real,fresh',response,pre⟩:=invoke u pending us eff pkt
      rw [tag] at response
      obtain ⟨heap,st,flag,recv,len,packet,kept⟩:=response
      exact ⟨a,v,real,heap,st,flag,by omega,len,recv.symm ▸ packet,fresh',preservedPorts_trans pre kept,heap⟩)
    refine ⟨a,t,run.mono ?_,keep,⟨rep,normal⟩,preservedPorts_trans ports (receive_ports heap frame)⟩
    change 4*(13*c.bufferRev.length+7)+allowance+4*(18*[b].length+9)+2 ≤ transferTime r s n S.clock L
    rw [length];rfl

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
