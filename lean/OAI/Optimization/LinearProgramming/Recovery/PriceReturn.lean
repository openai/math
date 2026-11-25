import OAI.Optimization.LinearProgramming.Recovery.OddReply
import OAI.Optimization.LinearProgramming.RAM.CallableScopedAccess
import OAI.Optimization.LinearProgramming.Recovery.NumericCall

/-! Publish the actual geometric scalar19 or its restart tag to the bit learner.
Under the two physical bank encodings these are scalar78 and address558. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Callable OracleSpec BitRAM

private def normalHeader : Block := .seq (.op (.addrConst recvBaseReg 3))
  (.seq (.op (.addrConst recvLenReg 1)) (.op (.addrConst statusReg 0)))

private def successful : Fragment := .seq (.ofBlock (.op (.copy (Odd.slot 3) (2*Odd.slot 19))))
  (Odd.leaf normalHeader)

def publish : Fragment := .seq (Odd.leaf (.op (.addrConst 0 1)))
  (.branch (.addrLT (Odd.slot 0) (2*Odd.slot 139)) (Odd.leaf (.op (.addrConst statusReg 1))) successful)

instance publish_fixedAccess : Fragment.FixedAccess publish := by
  unfold publish successful Odd.leaf
  infer_instance

variable {K : Type*}

def answerMemory (m : Memory K) (v : K) : Memory K :=
  ((((m.putIndex 0 1).putData 3 v).putIndex recvBaseReg 3).putIndex recvLenReg 1).putIndex statusReg 0

def restartMemory (m : Memory K) : Memory K := (m.putIndex 0 1).putIndex statusReg 1

theorem answer_packet [Zero K] [One K] (vm : Memory K) (b : Bool) :
    ScalarPacket (answerMemory vm (bitScalar b)) 3 [b] := by
  intro j hj
  have eq : j=0 := by simpa using hj
  subst j
  simp [answerMemory]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem header_eval {P : K→Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) normalHeader m 3 (((m.putIndex recvBaseReg 3).putIndex recvLenReg 1).putIndex statusReg 0) := by
  let a:=m.putIndex recvBaseReg 3
  let b:=a.putIndex recvLenReg 1
  have first:=Block.Eval.op_addrConst (safe:=Memory.AllData P) m recvBaseReg 3 h h
  have second:=Block.Eval.op_addrConst (safe:=Memory.AllData P) a recvLenReg 1 h h
  have third:=Block.Eval.op_addrConst (safe:=Memory.AllData P) b statusReg 0 h h
  exact first.seq (second.seq third)

theorem publish_restart {P : K→Prop} (minor g vm : Memory K) (hm : minor.AllData P)
    (hg : g.AllData P) (hv : vm.AllData P) (status : g.index 139=1) :
    publish.Run P (Odd.memory (Odd.memory minor g) vm) 10 (Odd.memory (Odd.memory minor g) (restartMemory vm)) := by
  let a:=Odd.memory minor g
  let v:=vm.putIndex 0 1
  have sa:=Odd.allData minor g hm hg
  have first:=Odd.leaf_run P a sa (Block.Eval.op_addrConst (safe:=Memory.AllData P) vm 0 1 hv hv)
  have guard : (Cond.addrLT (Odd.slot 0) (2*Odd.slot 139)).test (Odd.memory a v)=true := by
    have left : (Odd.memory a v).index (Odd.slot 0)=3 := by rw [Odd.index_slot]; rfl
    have right : (Odd.memory a v).index (2*Odd.slot 139)=2*(Odd.slot (g.index 139)) := by
      rw [Odd.index_even]; change 2*((Odd.memory minor g).index (Odd.slot 139)) = _; rw [Odd.index_slot]
    change decide ((Odd.memory a v).index (Odd.slot 0) < (Odd.memory a v).index (2*Odd.slot 139)) = true
    simpa only [left,right,status] using (show decide (3 < 2*Odd.slot 1) = true from by decide)
  have stop:=Odd.leaf_run P a sa (Block.Eval.op_addrConst (safe:=Memory.AllData P) v statusReg 1 hv hv)
  exact first.seq (Fragment.Run.branchTrue guard stop _)

theorem publish_answer {P : K→Prop} (minor g vm : Memory K) (hm : minor.AllData P)
    (hg : g.AllData P) (hv : vm.AllData P) (status : g.index 139=0) :
    publish.Run P (Odd.memory (Odd.memory minor g) vm) 18
      (Odd.memory (Odd.memory minor g) (answerMemory vm (g.data 19))) := by
  let a:=Odd.memory minor g
  let v:=vm.putIndex 0 1
  let w:=v.putData 3 (g.data 19)
  have sa:=Odd.allData minor g hm hg
  have first:=Odd.leaf_run P a sa (Block.Eval.op_addrConst (safe:=Memory.AllData P) vm 0 1 hv hv)
  have guard : (Cond.addrLT (Odd.slot 0) (2*Odd.slot 139)).test (Odd.memory a v)=false := by
    have left : (Odd.memory a v).index (Odd.slot 0)=3 := by rw [Odd.index_slot]; rfl
    have right : (Odd.memory a v).index (2*Odd.slot 139)=2*(Odd.slot (g.index 139)) := by
      rw [Odd.index_even]; change 2*((Odd.memory minor g).index (Odd.slot 139)) = _; rw [Odd.index_slot]
    change decide ((Odd.memory a v).index (Odd.slot 0) < (Odd.memory a v).index (2*Odd.slot 139)) = false
    simpa only [left,right,status] using (show decide (3 < 2*Odd.slot 0) = false from by decide)
  have hv' : v.AllData P := by
    intro j
    change P (vm.data j)
    exact hv j
  have hw : w.AllData P := hv'.putData 3 (hg 19)
  have val : (Odd.memory a v).data (2*Odd.slot 19)=g.data 19 := by simp [a]
  have after : (Odd.memory a v).putData (Odd.slot 3) ((Odd.memory a v).data (2*Odd.slot 19))=Odd.memory a w := by
    rw [val,Odd.putData]
  have hsafe : ((Odd.memory a v).putData (Odd.slot 3) ((Odd.memory a v).data (2*Odd.slot 19))).AllData P :=
    after.symm ▸ Odd.allData a w sa hw
  have cp:=Block.Eval.op_copy (safe:=Memory.AllData P) (Odd.memory a v) (Odd.slot 3) (2*Odd.slot 19)
    (Odd.allData a v sa hv) hsafe
  rw [after] at cp
  exact first.seq (Fragment.Run.branchFalse guard _ ((Fragment.Run.ofBlock cp).seq (Odd.leaf_run P a sa (header_eval w hw))))

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
