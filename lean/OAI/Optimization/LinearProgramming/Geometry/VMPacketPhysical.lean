import OAI.Optimization.LinearProgramming.BitRAM.IndexScript
import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import OAI.Optimization.LinearProgramming.RAM.UniformFootprint

/-! A 2-stride to 4-stride scalar copy between the nested RAM banks.
Physical address 75 holds the odd-encoded length. Registers 150 and 174 are
the twice-encoded geometry headers for its logical length and input base. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace VMPacketCopy

open RAM BitRAM.IndexScript

private def setupOps : List Instr :=
  [.addrCopy 1 87,.addrConst 3 1026,.addrConst 7 0,.addrConst 9 1,.addrConst 150 2,.addrConst 174 1026]
private def lengthOps : List Instr :=
  [.incr 9 9,.incr 9 9,.incr 7 7,.incr 150 150,.incr 150 150,.incr 150 150,.incr 150 150]
private def resetOps : List Instr :=
  [.addrConst 1 1,.addrConst 3 1,.addrConst 5 1,.addrConst 7 1,.addrConst 9 1]

def block : Block := .seq (.straight setupOps) <| .seq (.loop (.addrLT 9 75) (.straight lengthOps)) <|
  .seq (StrideCopy.block false 1 3 5 7 1 2 4) (.straight resetOps)

structure Physical {K : Type} (L B : ℕ) (s t : Memory K) : Prop where
  copied : ∀ j, j<L → t.data (4*(256+j)+2)=s.data (2*(B+j)+1)
  data : ∀ q, q≠1 → (∀ j, j<L → q≠4*(256+j)+2) → t.data q=s.data q
  length : t.index 150=4*L+2
  base : t.index 174=1026
  reset : ∀ q, q∈([1,3,5,7,9]:List ℕ) → t.index q=1
  index : ∀ q, q∉([1,3,5,7,9,150,174]:List ℕ) → t.index q=s.index q

private structure Counter {K : Type} (s : Memory K) (L B j : ℕ) (t : Memory K) : Prop where
  cursor : t.index 9=2*j+1
  length : t.index 7=j
  geomLength : t.index 150=4*j+2
  bound : t.index 75=2*L+1
  source : t.index 1=2*B+1
  target : t.index 3=1026
  geomBase : t.index 174=1026
  data : t.data=s.data

theorem physical_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (L B : ℕ) (hs : s.AllData P) (hB : 3≤B)
    (len : s.index 75=2*L+1) (src : s.index 87=2*B+1) :
    ∃ t, Block.Eval (Memory.AllData P) block s (20*L+14) t ∧ Physical L B s t := by
  let a : Memory K := ⟨s.data,BitRAM.IndexScript.run setupOps s.index⟩
  have setup : Block.Eval (Memory.AllData P) (.straight setupOps) s 6 a :=
    BitRAM.IndexScript.correct setupOps (by simp [setupOps,allowed]) s hs
  let I := fun (j : ℕ) (t : Memory K) => t.AllData P ∧ Counter s L B j t
  have ac : Counter s L B 0 a := by
    constructor <;> simp [a,setupOps,BitRAM.IndexScript.run,update,len,src]
  have body (j : ℕ) (hj : j<L) (m : Memory K) (H : I j m) :
      (Cond.addrLT 9 75).test m=true ∧ ∃ t, Block.Eval (Memory.AllData P) (.straight lengthOps) m 7 t ∧
        I (j+1) t := by
    obtain ⟨safe,h⟩ := H
    let t : Memory K := ⟨m.data,BitRAM.IndexScript.run lengthOps m.index⟩
    have e : Block.Eval (Memory.AllData P) (.straight lengthOps) m 7 t :=
      BitRAM.IndexScript.correct lengthOps (by simp [lengthOps,allowed]) m safe
    refine ⟨by simp [Cond.test,h.cursor,h.bound]; omega,t,e,e.safe_end,?_⟩
    constructor <;> simp [t,lengthOps,BitRAM.IndexScript.run,update,h.cursor,h.length,h.geomLength,
      h.bound,h.source,h.target,h.geomBase,h.data] <;> omega
  have stop (m : Memory K) (H : I L m) : (Cond.addrLT 9 75).test m=false ∧ m.AllData P :=
    ⟨by simp [Cond.test,H.2.cursor,H.2.bound],H.1⟩
  obtain ⟨b,eb,bs,bc⟩ := Block.Eval.loop_invariant_exact I a L 7 ⟨setup.safe_end,ac⟩ body stop
  obtain ⟨u,eu,bits,frame,_,_,_,idx⟩ := StrideCopy.block_correct P b false 1 3 5 7 1 2 4 L
    bs bc.length (by decide) (by decide) (by simp)
    (by intro j _; simp [StrideCopy.address,StrideCopy.move,bc.source]; omega)
    (by intro j _; simp [StrideCopy.address,StrideCopy.move,bc.target]; omega)
    (by intro i j _ _; simp [StrideCopy.address,StrideCopy.move,bc.source,bc.target]; omega)
  let t : Memory K := ⟨u.data,BitRAM.IndexScript.run resetOps u.index⟩
  have et : Block.Eval (Memory.AllData P) (.straight resetOps) u 5 t :=
    BitRAM.IndexScript.correct resetOps (by simp [resetOps,allowed]) u eu.safe_end
  have e : Block.Eval (Memory.AllData P) block s (20*L+14) t := by
    simpa only [block,show 6+(L*(7+2)+1+(L*(2+4+5)+2+5))=20*L+14 by omega] using
      setup.seq (eb.seq (eu.seq et))
  refine ⟨t,e,?_⟩
  constructor
  · intro j hj
    have v := bits j hj
    simp only [StrideCopy.address,StrideCopy.move,Bool.false_eq_true,↓reduceIte,bc.target,bc.source,bc.data] at v
    change u.data (4*(256+j)+2)=_
    rw [show 4*(256+j)+2=1026+4*j by omega,show 2*(B+j)+1=2*B+1+2*j by omega]
    exact v
  · intro q hq outside
    change u.data q=_
    apply (frame q hq ?_).trans (congrFun bc.data q)
    intro j hj
    have := outside j hj
    simp [StrideCopy.address,StrideCopy.move,bc.target]; omega
  · have hi := (idx 150 (by decide) (by decide) (by decide)).trans bc.geomLength
    simpa [t,resetOps,BitRAM.IndexScript.run,update] using hi
  · have hi := (idx 174 (by decide) (by decide) (by decide)).trans bc.geomBase
    simpa [t,resetOps,BitRAM.IndexScript.run,update] using hi
  · intro q hq
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp [t,resetOps,BitRAM.IndexScript.run,update]
  · intro q hq
    let permitted := ([1,3,5,7,9,150,174]:List ℕ).contains
    exact e.address_frame_of_list permitted (by rfl) (by rfl) q (by simpa [permitted] using hq)

end VMPacketCopy
end Geometry
end LinearProgramming
end Optimization
end OAI
