import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Read matrix output from the native even bank into protected logical caller scalars.
The native memory is preserved exactly. A logical address register supplies the native
index as an ordinary integer, so no conversion proportional to its value is required. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace BankRead

open RAM RAM.Callable

/-- An even encoded native pointer is exactly one less than its odd logical counterpart. -/
def readCell (logicalPtr scalar : ℕ) : Block :=
  .seq (.op (.decr (Odd.slot logicalPtr) (Odd.slot logicalPtr)))
    (.seq (.op (.load (Odd.slot scalar) (Odd.slot logicalPtr))) (.op (.incr (Odd.slot logicalPtr) (Odd.slot logicalPtr))))

/-- Read one native register as a logical count or pointer. -/
def receiveIndex (native logical : ℕ) : Block := .op (.incr (Odd.slot logical) (2*native))

private theorem memory_ext {K : Type*} {a b : Memory K} (d : ∀ i,a.data i=b.data i) (r : ∀ i,a.index i=b.index i) : a=b := by
  cases a; cases b; congr <;> funext i
  · exact d i
  · exact r i

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem receiveIndex_eval (P : K→Prop) (e m : Memory K) (he : e.AllData P) (hm : m.AllData P) (src dst : ℕ) :
    Block.Eval (Memory.AllData P) (receiveIndex src dst) (Odd.memory e m) 1 (Odd.memory e (m.putIndex dst (e.index src))) := by
  have safe := Odd.allData e m he hm
  have t : ((Odd.memory e m).putIndex (Odd.slot dst) ((Odd.memory e m).index (2*src)+1)).AllData P := safe
  have encoded : (Odd.memory e m).index (2*src)+1 = Odd.slot (e.index src) :=
    congrArg (fun i : ℕ => i+1) (Odd.index_even e m src)
  simpa only [receiveIndex, encoded, Odd.putIndex] using
    Block.Eval.op_incr (safe := Memory.AllData P) (Odd.memory e m) (Odd.slot dst) (2*src) safe t

theorem readCell_eval (P : K→Prop) (e m : Memory K) (he : e.AllData P) (hm : m.AllData P)
    (ptr scalar : ℕ) :
    Block.Eval (Memory.AllData P) (readCell ptr scalar) (Odd.memory e m) 3
      (Odd.memory e (m.putData scalar (e.data (m.index ptr)))) := by
  let phys:=Odd.memory e m
  let src:=2*m.index ptr
  let a:=phys.putIndex (Odd.slot ptr) src
  let b:=a.putData (Odd.slot scalar) (e.data (m.index ptr))
  let t:=b.putIndex (Odd.slot ptr) (src+1)
  have sp : phys.AllData P := Odd.allData e m he hm
  have sa : a.AllData P := sp
  have sb : b.AllData P := sa.putData _ (he _)
  have decoded : phys.index (Odd.slot ptr) - 1 = src :=
    (congrArg (fun i : ℕ => i-1) (Odd.index_slot e m ptr)).trans
      (Nat.add_sub_cancel (2*m.index ptr) 1)
  have ea : Block.Eval (Memory.AllData P) (.op (.decr (Odd.slot ptr) (Odd.slot ptr))) phys 1 a := by
    simpa only [a, decoded] using
      Block.Eval.op_decr (safe := Memory.AllData P) phys (Odd.slot ptr) (Odd.slot ptr) sp sp
  have addr : a.index (Odd.slot ptr) = src := Memory.putIndex_same ..
  have payload : a.data (a.index (Odd.slot ptr)) = e.data (m.index ptr) :=
    (congrArg a.data addr).trans (Odd.data_even e m (m.index ptr))
  have eb : Block.Eval (Memory.AllData P) (.op (.load (Odd.slot scalar) (Odd.slot ptr))) a 1 b := by
    simpa only [b, payload] using
      Block.Eval.op_load (safe := Memory.AllData P) a (Odd.slot scalar) (Odd.slot ptr)
        sa (sa.putData _ (sa _))
  have saved : b.index (Odd.slot ptr) = src := addr
  have et : Block.Eval (Memory.AllData P) (.op (.incr (Odd.slot ptr) (Odd.slot ptr))) b 1 t := by
    simpa only [t, saved] using
      Block.Eval.op_incr (safe := Memory.AllData P) b (Odd.slot ptr) (Odd.slot ptr) sb sb
  have eq : t = Odd.memory e (m.putData scalar (e.data (m.index ptr))) := by
    calc
      t = phys.putData (Odd.slot scalar) (e.data (m.index ptr)) := by
        apply memory_ext
        · intro i
          rfl
        · intro i
          by_cases hi : i = Odd.slot ptr
          · subst i
            exact (Memory.putIndex_same b (Odd.slot ptr) (src+1)).trans (Odd.index_slot e m ptr).symm
          · exact (Memory.putIndex_ne b hi (src+1)).trans (Memory.putIndex_ne phys hi src)
      _ = Odd.memory e (m.putData scalar (e.data (m.index ptr))) := Odd.putData e m scalar _
  exact eq ▸ ea.seq (eb.seq et)

private def copyOps : List Instr := [.store 181 4,.incr 180 180,.incr 181 181,.incr 183 183]
def body : Block := .seq (readCell 180 4) (Odd.block (.straight copyOps))
def copyWindow : Block := .seq (Odd.block (.op (.addrConst 183 0))) (.loop (Odd.cond (.addrLT 183 182)) body)

/-- The two banks may use the same numeric bases. Original field inputs and the fresh
native solver state are never aliased with the caller's destination. -/
theorem copyWindow_eval (P : K→Prop) (e m : Memory K) (he : e.AllData P) (sm : m.AllData P)
    (src dst n : ℕ) (h180 : m.index 180=src) (h181 : m.index 181=dst) (h182 : m.index 182=n) (hd : 5 ≤ dst) :
    ∃ t k, k ≤ 21*n+5 ∧ Block.Eval (Memory.AllData P) copyWindow (Odd.memory e m) k (Odd.memory e t) ∧
      (∀ j < n,t.data (dst+j)=e.data (src+j)) ∧
      (∀ p,p≠4→(p < dst ∨ dst+n ≤ p)→t.data p=m.data p) ∧
      t.index 180=src+n ∧ t.index 181=dst+n ∧ t.index 183=n ∧
      ∀ p,p≠180→p≠181→p≠183→t.index p=m.index p := by
  let At (j : ℕ) (v : Memory K) := v.AllData P ∧ v.index 180=src+j ∧ v.index 181=dst+j ∧ v.index 183=j ∧
    (∀ p,p≠180→p≠181→p≠183→v.index p=m.index p) ∧ (∀ q < j,v.data (dst+q)=e.data (src+q)) ∧
    (∀ p,p≠4→(p < dst ∨ dst+j ≤ p)→v.data p=m.data p)
  let I (j : ℕ) (phys : Memory K) := ∃ v,phys=Odd.memory e v ∧ At j v
  let a:=m.putIndex 183 0
  obtain ⟨ik,hik,init⟩:=Odd.block_eval P e he (Block.Eval.op_addrConst m 183 0 sm (show a.AllData P from sm))
  have start : I 0 (Odd.memory e a) := by
    refine ⟨a,rfl,sm,?_,?_,?_,?_,by simp,fun _ _ _=>rfl⟩
    · simp [a,h180]
    · simp [a,h181]
    · simp [a]
    · intro p _ _ hp; exact Memory.putIndex_ne _ hp _
  have step (j : ℕ) (hj : j < n) (z : Memory K) (hz : I j z) :
      (Odd.cond (.addrLT 183 182)).test z=true ∧ ∃ t k,k ≤ 19 ∧ Block.Eval (Memory.AllData P) body z k t ∧ I (j+1) t := by
    obtain ⟨v,rfl,vh,vsrc,vdst,vc,vi,done,frame⟩:=hz
    have vlen := (vi 182 (by decide) (by decide) (by decide)).trans h182
    have test : (Odd.cond (.addrLT 183 182)).test (Odd.memory e v)=true := by rw [Odd.cond_test];simp [Cond.test,vc,vlen,hj]
    let b:=v.putData 4 (e.data (v.index 180))
    let c:=b.putData (b.index 181) (b.data 4)
    let f:=c.putIndex 180 (c.index 180+1)
    let g:=f.putIndex 181 (f.index 181+1)
    let t:=g.putIndex 183 (g.index 183+1)
    have sb : b.AllData P := vh.putData _ (he _)
    have sc : c.AllData P := sb.putData _ (sb _)
    have ef := Block.Eval.op_incr c 180 180 sc (show f.AllData P from sc)
    have eg := Block.Eval.op_incr f 181 181 (show f.AllData P from sc) (show g.AllData P from sc)
    have et := Block.Eval.op_incr g 183 183 (show g.AllData P from sc) (show t.AllData P from sc)
    have ops : Block.Eval (Memory.AllData P) (.straight copyOps) b 4 t :=
      (Block.Eval.op_store b 181 4 sb sc).seq (ef.seq (eg.seq (et.seq (.skip sc))))
    obtain ⟨k,hk,run⟩:=Odd.block_eval P e he ops
    have get:=readCell_eval P e v he vh 180 4
    refine ⟨test,Odd.memory e t,_,by omega,get.seq run,t,rfl,sc,?_,?_,?_,?_,?_,?_⟩
    · simp [t,g,f,c,b,vsrc,Nat.add_assoc]
    · simp [t,g,f,c,b,vdst,Nat.add_assoc]
    · simp [t,g,f,c,b,vc]
    · intro p x y z;simpa [t,g,f,c,b,Memory.putIndex_ne _ x,Memory.putIndex_ne _ y,Memory.putIndex_ne _ z] using vi p x y z
    · intro q hq;by_cases eq : q=j
      · subst q;simp [t,g,f,c,b,vdst,vsrc]
      · have go : dst+q≠dst+j := by omega
        have g4 : dst+q≠4 := by omega
        simpa [t,g,f,c,b,vdst,Memory.putData_ne _ go,Memory.putData_ne _ g4] using done q (by omega)
    · intro p h4 outside
      have ne : p≠dst+j := by omega
      simpa [t,g,f,c,b,vdst,Memory.putData_ne _ ne,Memory.putData_ne _ h4] using frame p h4 (by omega)
  have stop (z : Memory K) (h : I n z) : (Odd.cond (.addrLT 183 182)).test z=false ∧ z.AllData P := by
    obtain ⟨v,rfl,vh,_,_,vc,vi,_,_⟩:=h
    refine ⟨?_,Odd.allData e v he vh⟩
    rw [Odd.cond_test];simp [Cond.test,vc,(vi 182 (by decide) (by decide) (by decide)).trans h182]
  obtain ⟨u,k,hk,loop,⟨t,rfl,_,a,b,c,indices,contents,frame⟩⟩:=Block.Eval.loop_invariant I (Odd.memory e a) n 19 start step stop
  exact ⟨t,_,by omega,init.seq loop,contents,frame,a,b,c,indices⟩

end BankRead
end Recovery
end LinearProgramming
end Optimization
end OAI
