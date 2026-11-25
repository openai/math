import OAI.Optimization.LinearProgramming.Recovery.MaskedLayout
import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM
import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! The reentrant subspace call reads a row-major opposite basis followed by n support
flags. The first copy protects every raw entry, including scalar zero, before the
flags are moved past the enlarged equation table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace MaskedInput
open RAM RAM.Tape RAM.Call Geometry

def bundle {K : Type} [Zero K] [One K] {h n : ℕ} (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) : List K :=
  encodedGramInput E++List.ofFn (fun j : Fin n=>if j∈S then 1 else 0)

def headers : HeaderPlan 206 :=
  let h : AddressTerm 206:=.reg 28
  let n : AddressTerm 206:=.reg 29
  [(28,.reg 0),(29,.reg 1),(2,h*n+n),(24,(.val 256)+(.reg 2)),(161,(.reg 24)+h*n),(162,(.reg 161)+n*n),
    (200,h+n),(201,n),(202,.reg 24),(203,(.reg 162)+n),(204,(.reg 203)+n*n),(205,.val 0),
    (0,.val 0),(1,.reg 24),(3,.val 0)]

private def copyFlags : List Instr := [.addrCopy 0 161,.addrCopy 1 162,.addrCopy 2 29,.addrConst 3 0]
private def diagonalHeader : List Instr := [.addrConst 14 0,.addrCopy 31 29,.addrCopy 33 29,.addrCopy 35 161]

def snapshot : Block := .seq (HeaderPlan.code 220 headers) (.seq (PrimalDual.copyWindow false)
  (.seq (.straight copyFlags) (.seq (PrimalDual.copyWindow false) (.straight diagonalHeader))))

noncomputable def time (h n : ℕ) := headers.budget.eval (h+n)+(7*words h n+1)+(4+(7*n+1)+4)

structure Header {K : Type*} (h n : ℕ) (m : Memory K) : Prop where
  zero : m.index 14=0
  rows : m.index 31=n
  cols : m.index 33=n
  diagonal : m.index 35=bottom h n
  flags : m.index 162=flagBase h n
  count : m.index 200=h+n
  width : m.index 201=n
  matrix : m.index 202=base h n
  output : m.index 203=outputBase h n
  scratch : m.index 204=scratchBase h n
  dirty : m.index 205=0

private def initialEnv (h n : ℕ) (i : Fin 206) := ([h,n][i.val]?).getD 0

private theorem initialBound (h n : ℕ) (i : Fin 206) : initialEnv h n i ≤ h+n := by
  by_cases ha : i.val=0
  · simp [initialEnv,ha]
  by_cases hb : i.val=1
  · simp [initialEnv,hb]
  have lo : [h,n].length ≤ i.val := by simp only [List.length_cons,List.length_nil];omega
  simp [initialEnv,List.getElem?_eq_none lo]

private theorem parameters (h n : ℕ) : let ix:=headers.output (initialEnv h n)
    ix 0=0 ∧ ix 1=base h n ∧ ix 2=words h n ∧ ix 3=0 ∧ ix 29=n ∧ ix 161=bottom h n ∧
    ix 162=flagBase h n ∧ ix 200=h+n ∧ ix 201=n ∧ ix 202=base h n ∧ ix 203=outputBase h n ∧
    ix 204=scratchBase h n ∧ ix 205=0 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

variable {K : Type} {h n : ℕ}

private theorem offset_lt (a : Fin h) (b : Fin n) : a.val*n+b.val < h*n := by
  have v:=Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
  rw [Nat.succ_mul] at v;omega

private theorem originalMatrix [Zero K] [One K] (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) (a : Fin h) (b : Fin n) :
    ((bundle E S)[a.val*n+b.val]?).getD 0=E a b := by
  have reach : a.val*n+b.val < (encodedGramInput E).length := by simpa using offset_lt a b
  rw [bundle,List.getElem?_append_left reach]
  exact congrFun (congrFun (gramInputMatrix_encoded E) a) b

private theorem originalFlag [Zero K] [One K] (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) (j : Fin n) :
    ((bundle E S)[h*n+j.val]?).getD 0=if j∈S then 1 else 0 := by
  rw [bundle,List.getElem?_append_right (by simp)]
  simp [j.isLt]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem snapshot_run (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) (P : K→Prop)
    (input : ∀ j:ℕ,P (((bundle E S)[j]?).getD 0)) :
    ∃ t c,c ≤ time h n ∧ Block.Eval (Memory.AllData P) snapshot (start [h,n] (bundle E S)).memory c t ∧
      Header h n t ∧ uniformRect h n (base h n) t=E ∧
      ∀j : Fin n,t.data (flagBase h n+j.val)=if j∈S then 1 else 0 := by
  let first:=(start [h,n] (bundle E S)).memory
  obtain ⟨u,k,pre,clock,ud,ui⟩:=headers.correct 220 (by decide) first (initialEnv h n) (fun _=>rfl)
    (show first.AllData P from input)
  obtain ⟨p0,p1,p2,p3,p29,p161,p162,p200,p201,p202,p203,p204,p205⟩:=parameters h n
  obtain ⟨v,copy,data,_,regs⟩:=PrimalDual.copyWindow_correct false (words h n) 0 (base h n) u pre.safe_end
    ((ui 0).trans p0) ((ui 1).trans p1) ((ui 2).trans p2) ((ui 3).trans p3)
    (Or.inl (by simp [base])) (by simp [base])
  have r29:=(regs 29 (by decide)).trans ((ui 29).trans p29)
  have r161:=(regs 161 (by decide)).trans ((ui 161).trans p161)
  have r162:=(regs 162 (by decide)).trans ((ui 162).trans p162)
  let a : Memory K:=⟨v.data,BitRAM.IndexScript.run copyFlags v.index⟩
  have choose : Block.Eval (Memory.AllData P) (.straight copyFlags) v 4 a:=
    BitRAM.IndexScript.correct copyFlags (by simp [copyFlags,BitRAM.IndexScript.allowed]) v copy.safe_end
  have square : n ≤ n*n:=by cases n <;> simp [Nat.succ_mul]
  obtain ⟨w,second,flags,unchanged,high⟩:=PrimalDual.copyWindow_correct false n (bottom h n) (flagBase h n) a choose.safe_end
    r161 r162 r29 rfl (Or.inl (Nat.add_le_add_left square _))
    (show 0 < flagBase h n by unfold flagBase bottom base; omega)
  let t : Memory K:=⟨w.data,BitRAM.IndexScript.run diagonalHeader w.index⟩
  have finish : Block.Eval (Memory.AllData P) (.straight diagonalHeader) w 4 t:=
    BitRAM.IndexScript.correct diagonalHeader (by simp [diagonalHeader,BitRAM.IndexScript.allowed]) w second.safe_end
  have addr (i : Fin 206) (lo : 4 ≤ i.val) : w.index i.val=headers.output (initialEnv h n) i := by
    have ai : a.index i.val=v.index i.val:=by
      simp [a,copyFlags,BitRAM.IndexScript.run,BitRAM.IndexScript.update,Function.update,show i.val≠0 by omega,
        show i.val≠1 by omega,show i.val≠2 by omega,show i.val≠3 by omega]
    exact (high _ lo).trans (ai.trans ((regs _ lo).trans (ui i)))
  have header : Header h n t:=⟨rfl,(addr 29 (by decide)).trans p29,(addr 29 (by decide)).trans p29,
    (addr 161 (by decide)).trans p161,(addr 162 (by decide)).trans p162,(addr 200 (by decide)).trans p200,
    (addr 201 (by decide)).trans p201,(addr 202 (by decide)).trans p202,(addr 203 (by decide)).trans p203,
    (addr 204 (by decide)).trans p204,(addr 205 (by decide)).trans p205⟩
  have saved (j : ℕ) (hj : j < words h n) : v.data (base h n+j)=((bundle E S)[j]?).getD 0 := by
    have read:=data j hj
    simp only [Nat.zero_add] at read
    exact read.trans (congrFun ud j)
  have total:=clock.trans (headers.cost_le _ _ (initialBound h n))
  refine ⟨t,_,?_,pre.seq (copy.seq (choose.seq (second.seq finish))),header,?_,?_⟩
  · unfold time;omega
  · ext i j
    let offset:=i.val*n+j.val
    have less : offset < h*n:=offset_lt i j
    have below : base h n+offset < flagBase h n:=by unfold flagBase bottom;omega
    have nonzero : base h n+offset≠0:=by unfold base;omega
    change w.data (base h n+i.val*n+j.val)=E i j
    rw [Nat.add_assoc];exact (unchanged _ nonzero (Or.inl below)).trans ((saved offset (by unfold words;omega)).trans (originalMatrix E S i j))
  · intro j
    change w.data (flagBase h n+j.val)=_
    have original:=saved (h*n+j.val) (by unfold words;omega)
    have same : bottom h n+j.val=base h n+(h*n+j.val):=by unfold bottom;omega
    have readFlag : a.data (bottom h n+j.val) = if j∈S then 1 else 0 := by
      change v.data (bottom h n+j.val) = _
      rw [same]
      exact original.trans (originalFlag E S j)
    exact (flags j.val j.isLt).trans readFlag

end MaskedInput
end Recovery
end LinearProgramming
end Optimization
end OAI
