import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout
import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import OAI.Optimization.LinearProgramming.NativePrice.Tape

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM BitRAM OracleSpec NativePrice

/-- Separate the flat output packet from the fixed scalar parser scratch. This works
also for the minimum native packet base three and for a one-bit restart packet. -/
def promoteFlatReply : Block := .seq (seekBlock 43 45 46 37) <| .seq (.op (.addrConst 47 10)) <|
  .seq (seekBlock 45 48 46 47) (.seq (.op (.addrCopy 3 48)) (StrideCopy.block false 43 48 46 37 0 1 1))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem promoteFlatReply_spec (m : Memory K) (w : Word) {P : K → Prop}
    (hm : m.AllData P) (len : m.index 37=w.length) (base : 3 ≤ m.index 43)
    (packet : ScalarPacket m (m.index 43) w) :
    ∃ t, Block.Eval (Memory.AllData P) promoteFlatReply m (11*w.length+50) t ∧
      t.index 37=w.length ∧ 10 ≤ t.index 3 ∧ WordAt t (t.index 3) w := by
  let L := w.length
  let B := m.index 43
  let target := B+L+10
  obtain ⟨a,e1,ad,_,ap,ai⟩ := seekBlock_correct P m 43 45 46 37 L (by decide) (by decide) (by decide) len hm
  let b := a.putIndex 47 10
  have sa : a.AllData P := e1.safe_end
  have e2 := Block.Eval.op_addrConst (safe := Memory.AllData P) a 47 10 sa (sa.putIndex _ _)
  obtain ⟨c,e3,cd,_,cp,ci⟩ := seekBlock_correct P b 45 48 46 47 10 (by decide) (by decide) (by decide) (by simp [b]) e2.safe_end
  let z := c.putIndex 3 (c.index 48)
  have cs : c.AllData P := e3.safe_end
  have e4 := Block.Eval.op_addrCopy (safe := Memory.AllData P) c 3 48 cs (cs.putIndex _ _)
  have ls : z.index 37=L := by
    rw [show z.index 37=c.index 37 from Memory.putIndex_ne _ (by decide) _,ci 37 (by decide) (by decide)]
    simpa [b] using (ai 37 (by decide) (by decide)).trans len
  have bs : z.index 43=B := by
    rw [show z.index 43=c.index 43 from Memory.putIndex_ne _ (by decide) _,ci 43 (by decide) (by decide)]
    simpa [b,B] using ai 43 (by decide) (by decide)
  have dst : c.index 48=target := by simpa [target,B,L,b,ap] using cp
  have zs : z.index 48=target := by simpa [z] using dst
  have save : z.index 3=target := by simpa [z] using dst
  have dframe : z.data=m.data := cd.trans ad
  have e5 := StrideCopy.block_correct P z false 43 48 46 37 0 1 1 L e4.safe_end ls (by decide)
    (by decide) (by simp) (fun j hj => by
      simp [StrideCopy.address,StrideCopy.move,bs,B]
      omega)
    (fun j hj => by simp [StrideCopy.address,StrideCopy.move,zs,target])
    (fun a j _ hj => by
      simp [StrideCopy.address,StrideCopy.move,bs,zs,target]
      omega)
  obtain ⟨t,copy,values,_,_,_,_,ti⟩ := e5
  have tp : t.index 3=target := (ti 3 (by decide) (by decide) (by decide)).trans save
  have scalarInvariant : (fun m : Memory K => ∀ i, P (m.data i)) = Memory.AllData P := by
    funext s
    rfl
  rw [scalarInvariant] at e1 e3
  refine ⟨t,?_,(ti 37 (by decide) (by decide) (by decide)).trans ls,?_,?_⟩
  · simpa only [promoteFlatReply,L,show 4*L+3+(1+(4*10+3+(1+(L*(1+1+5)+2))))=11*L+50 by omega] using e1.seq (e2.seq (e3.seq (e4.seq copy)))
  · rw [tp]; dsimp [target]; omega
  · intro i hi
    have eq : t.data (target+i)=m.data (B+i) := by
      simpa [StrideCopy.address,StrideCopy.move,bs,zs,dframe] using values i hi
    rw [tp,eq]; have bit := packet i hi
    cases hb : w[i] with
    | false => simpa [BitRAM.bitScalar,hb,B] using bit
    | true => simpa [BitRAM.bitScalar,hb,B] using bit

end Compression
end LinearProgramming
end Optimization
end OAI
