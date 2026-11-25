import OAI.Hierarchy.DescentResetPeerJointAux

namespace OAI
/-! # Original inverse, predecessor roster and retained numeric decoder at the auxiliary writer -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentDyadicSpan DescentSixParty.Chronology DescentResetPeerJointRAM DescentPackedZip DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H P O D G M b N : ℕ}

structure Registers (base width : ℕ) (A : Sources) (raw : Bank) (name : Fin N→Fin P)
    (old : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P)) (m : Memory w) : Prop where
  count : A.count.read m (0:Word w)=(N:Word w)
  inverse : ∀s,A.inverse.read m ((s:Fin N).val:Word w)=((name s).val:Word w)
  ports : ∀(r:Fin O) (i:Fin D),A.prior.read m ((r.val*D+i.val:ℕ):Word w)=(((old r i).elim O Fin.val : ℕ):Word w)
  lut : ∀(f:Fin 3)(x:Fin P),(table base P f.val).read m (x.val:Word w)=(field width D f.val x.val:Word w)
  nearWords : ∀v j,m (raw.base+(j:Fin 3).val*P+(v:Fin P).val)=(((near v j).elim P Fin.val : ℕ):Word w)

theorem registers (base width : ℕ) (A : Sources) (raw : Bank) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (old : Fin O→Fin D→Option (Fin O))
    (near : Fin P→Fin 3→Option (Fin P)) (m : Memory w)
    (room : Room A base H P O D w) (prior : raw.Fits w base) (size : 3*P≤raw.size)
    (stored : Reads A N name now old m)
    (original : ∀v j,m (raw.base+(j:Fin 3).val*P+(v:Fin P).val)=(((near v j).elim P Fin.val : ℕ):Word w))
    (roof : DescentResetPeerJointPacked.endAddress base H P G M b < 2^w) :
    Registers base width A raw name old near ((DescentResetPeerJointPacked.phase w base H P O width D G M b A).image m) := by
  let one:=DescentResetPeerJointPacked.phase w base H P O width D G M b A
  have first:=DescentResetPeerJointPacked.any base width A m room roof
  have keep (bank : Bank) (safe : bank.Fits w base) {i : ℕ} (inside : i<bank.size) :
      bank.read (one.image m) (i:Word w)=m (bank.base+i) :=
    (bank_read bank _ inside safe).trans (first.2 _ (.inl ((Nat.add_lt_add_left inside _).trans_le safe.2.2)))
  refine ⟨?_,fun s=>(keep _ room.inverse (s.isLt.trans_le stored.inverseSize)).trans (stored.inverse s),?_,?_,?_⟩
  · exact (keep _ room.count (i:=0) room.count.1).trans (by simpa using stored.count)
  · intro r i
    have u:=Nat.mul_le_mul_right D r.isLt
    rw [Nat.succ_mul] at u
    exact (keep _ room.prior (show r.val*D+i.val<A.prior.size by have hi:=i.isLt;have le:=room.oldRows;omega)).trans (stored.prior r i)
  · intro f x
    have inside:=x.isLt.trans_le (span_ge P)
    have fit:=table_fits base H P f.isLt room.stop
    let a:=(table base P f.val).base+x.val
    have before : a<outputBase base P := (Nat.add_lt_add_left inside _).trans_le fit.2.2
    let primary:=DescentResetPeerJointRAM.phase w base H P O width D A
    have early : a<DescentResetPeerJointRAM.endAddress base H P := before.trans_le (by unfold DescentResetPeerJointRAM.endAddress;omega)
    have scatter := DescentFixedRowProgram.frame (outputBase base P) (4*H)
      (DescentResetPeerJointRAM.row A base H P O D) ((deck w base P width D).image m) a (.inl before)
    have pack := DescentStaticWordColumn.frame (DescentResetPeerJointRAM.endAddress base H P)
      (DescentResetHaloBroadcast.count H G M b) (DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H))
      (primary.image m) a (.inl early)
    exact (bank_read _ _ inside fit).trans (pack.trans (scatter.trans
      ((bank_read _ _ inside fit).symm.trans (field_read base H P width D m room.stop f x))))
  · intro v j
    have u:=Nat.mul_le_mul_right P j.isLt
    rw [Nat.succ_mul] at u
    have bound : raw.base+j.val*P+v.val<base := by have h:=v.isLt;have end_:=prior.2.2;omega
    exact (first.2 _ (.inl bound)).trans (original v j)

private theorem ltWord {a c : ℕ} (ha : a<2^w) (hc : c<2^w) :
    Comparison.lt.test (a:Word w) (c:Word w)=decide (a<c) := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hc]

theorem sample (base width : ℕ) (A : Sources) (raw : Bank) (name : Fin N→Fin P)
    (old : Fin O→Fin D→Option (Fin O)) (near : Fin P→Fin 3→Option (Fin P)) (m : Memory w)
    (nFit : N≤H) (room : Room A base H P O D w) (prior : raw.Fits w base) (size : 3*P≤raw.size)
    (regs : Registers base width A raw name old near m) (v : Fin H) (j : Fin 4) :
    (scalar A raw base P O D v.val j.val).eval m 0=(value width name old near v j : Word w) := by
  classical
  by_cases correction : j.val=3
  · simp only [scalar,value,ite_eq_left correction]
    exact DescentResetPeerOldCorrection.eval base width A name old m nFit room v regs.count regs.inverse regs.ports
      (regs.lut 0) (regs.lut 2)
  simp only [scalar,value,ite_eq_right correction]
  let here:=Expr.lookup A.inverse (.lit v.val)
  let root:=Expr.lookup (table base P 0) here
  let offset:=Expr.lookup (table base P 2) here
  let oldPorts := fun i : Fin D => Expr.lookup A.prior (.op .add offset (.lit i.val))
  let payload:=if j.val=0 then Expr.lit 0 else Expr.lookup (table base P 1) here
  change (if Comparison.lt.test (v.val:Word w) (A.count.read m 0) then _ else 0)=_
  rw [regs.count,ltWord (v.isLt.trans room.newWidth) (nFit.trans_lt room.newWidth)]
  by_cases live : v.val<N
  · simp only [live,decide_true,ite_true,dite_eq_left]
    let s : Fin N:=⟨v.val,live⟩
    let x:=name s
    have r : here.eval m 0=(x.val:Word w):=regs.inverse s
    have oldRoot : root.eval m 0=((x.val/width:ℕ):Word w) :=
      (congrArg ((table base P 0).read m) r).trans (regs.lut 0 x)
    have begin_ : offset.eval m 0=((x.val/width*D:ℕ):Word w) :=
      (congrArg ((table base P 2).read m) r).trans (regs.lut 2 x)
    have pFit : P<2^w := by have e:=room.stop;have sp:=span_ge P;dsimp [DescentResetPeerJointRAM.endAddress,outputBase] at e;omega
    by_cases absent : j.val=2
    · simp only [absent,ite_true]
      have test:=DescentResetPeerMissingSelf.read raw P here m 0 x (near x) prior size pFit r (regs.nearWords x)
      change (DescentResetPeerMissingSelf.missing raw P here).eval m 0=
        ((if ∀t,near x t≠some x then 1 else 0 : ℕ):Word w)
      rw [test]
      split <;> rfl
    · simp only [absent,ite_false]
      change (if Comparison.lt.test (root.eval m 0) (O:Word w) then
        (DescentClosedHaloChip.chip oldPorts root root payload).eval m 0 else 0)=_
      rw [oldRoot,ltWord ((Nat.div_le_self ..).trans_lt (x.isLt.trans pFit)) room.oldWidth]
      by_cases valid : x.val/width<O
      · have located : (name ⟨v.val,live⟩).val/width<O := valid
        simp only [valid,located,decide_true,ite_true,dite_eq_left]
        let t : Fin O:=⟨x.val/width,valid⟩
        have pv : payload.eval m 0=((if j.val=0 then 0 else x.val%width*radix D : ℕ):Word w) := by
          by_cases z:j.val=0
          · simp [payload,z,Expr.eval]
          · simp only [payload,ite_eq_right z]
            exact (congrArg ((table base P 1).read m) r).trans (regs.lut 1 x)
        refine DescentClosedHaloChip.eval (old t) t t _ oldPorts root root payload m 0 room.oldWidth ?_ oldRoot oldRoot pv
        intro i
        simp only [oldPorts,Expr.eval,begin_,RowOp.opcode,BinaryOp.eval,←Nat.cast_add]
        exact regs.ports t i
      · simp [valid,x,s] at *
  · simp [live]

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
