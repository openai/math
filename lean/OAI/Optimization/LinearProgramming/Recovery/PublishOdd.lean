import OAI.Optimization.LinearProgramming.Recovery.Publish
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Publish a high logical caller vector through the final ordinary RAM output ABI.
The raw length is counted from its odd address encoding without converting field data. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Publish
open RAM RAM.Callable BitRAM.IndexScript

private def headerOps (tag : ℕ) : List Instr := [.addrCopy 14 (Odd.slot 210),.addrConst 15 0,.addrConst 13 1,.addrConst 16 tag]
private def countOps : List Instr := [.incr 15 15,.incr 13 13,.incr 13 13]
private def untagLength : Block := .loop (.addrLT 13 (Odd.slot 211)) (.straight countOps)

def fromOdd (tag : ℕ) : Block := .seq (.straight (headerOps tag)) (.seq untagLength (.seq block (.op (.addrConst 17 0))))

def oddTime (n : ℕ) := 4+(5*n+1)+(8*(n-1)+8)+1

theorem oddTime_le (n : ℕ) : oddTime n ≤ 13*n+14 := by unfold oddTime;omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem count (P : K→Prop) (n src tag : ℕ) (left : ℕ) : ∀ j m,j+left=n → m.AllData P →
    m.index 13=2*j+1 → m.index 15=j → m.index (Odd.slot 211)=Odd.slot n → m.index 14=src → m.index 16=tag →
    ∃ u,Block.Eval (Memory.AllData P) untagLength m (5*left+1) u ∧ u.data=m.data ∧
      u.index 14=src ∧ u.index 15=n ∧ u.index 16=tag := by
  induction left with
  | zero =>
    intro j m h safe pos cur endPos source ret
    have guard : (Cond.addrLT 13 (Odd.slot 211)).test m=false := by
      change decide (m.index 13 < m.index (Odd.slot 211)) = false
      rw [pos,endPos]
      exact decide_eq_false (show ¬ 2*j+1 < 2*n+1 by omega)
    refine ⟨m,?_,rfl,source,by omega,ret⟩
    change Block.Eval (Memory.AllData P) (.loop (.addrLT 13 (Odd.slot 211)) (.straight countOps)) m 1 m
    exact .loopFalse guard safe
  | succ left ih =>
    intro j m h safe pos cur endPos source ret
    have guard : (Cond.addrLT 13 (Odd.slot 211)).test m=true := by
      change decide (m.index 13 < m.index (Odd.slot 211)) = true
      rw [pos,endPos]
      exact decide_eq_true (show 2*j+1 < 2*n+1 by omega)
    let a : Memory K:=⟨m.data,BitRAM.IndexScript.run countOps m.index⟩
    have step : Block.Eval (Memory.AllData P) (.straight countOps) m 3 a:=correct countOps (by simp [countOps,allowed]) m safe
    have ap : a.index 13=2*(j+1)+1 := by change m.index 13+1+1=2*(j+1)+1;omega
    have ac : a.index 15=j+1 := by change m.index 15+1=j+1;omega
    obtain ⟨u,rest,ud,u14,u15,u16⟩:=ih (j+1) a (by omega) step.safe_end ap ac endPos source ret
    refine ⟨u,?_,ud,u14,u15,u16⟩
    change Block.Eval (Memory.AllData P) (.loop (.addrLT 13 (Odd.slot 211)) (.straight countOps)) a (5*left+1) u at rest
    rw [show 5*(left+1)+1 = 1+3+1+(5*left+1) by omega]
    change Block.Eval (Memory.AllData P) (.loop (.addrLT 13 (Odd.slot 211)) (.straight countOps)) m (1+3+1+(5*left+1)) u
    exact .loopTrue guard step rest

theorem fromOdd_spec (tag n src : ℕ) (native caller : Memory K) (v : Fin n→K) (P : K→Prop)
    (hnat : native.AllData P) (hcaller : caller.AllData P) (positive : 0<n) (sep : n ≤ Odd.slot src)
    (p210 : caller.index 210=src) (p211 : caller.index 211=n) (wire : ∀i : Fin n,caller.data (src+i.val)=v i) :
    ∃ t,Block.Eval (Memory.AllData P) (fromOdd tag) (Odd.memory native caller) (oddTime n) t ∧
      (∀i : Fin n,t.data i.val=v i) ∧ t.index 16=tag ∧ t.index 17=0 := by
  let start:=Odd.memory native caller
  let a : Memory K:=⟨start.data,BitRAM.IndexScript.run (headerOps tag) start.index⟩
  have first : Block.Eval (Memory.AllData P) (.straight (headerOps tag)) start 4 a:=
    correct (headerOps tag) (by simp [headerOps,allowed]) start (Odd.allData native caller hnat hcaller)
  have addr : a.index 14=Odd.slot src := by
    change start.index (Odd.slot 210)=Odd.slot src;rw [Odd.index_slot,p210]
  have len : a.index (Odd.slot 211)=Odd.slot n:=by
    change start.index (Odd.slot 211)=Odd.slot n;rw [Odd.index_slot,p211]
  obtain ⟨u,loop,data,u14,u15,u16⟩:=count P n (Odd.slot src) tag n 0 a (by omega) first.safe_end rfl rfl len addr rfl
  have packed (i : Fin n) : u.data (Odd.slot src+2*i.val)=v i := by
    rw [data]
    change start.data (Odd.slot src+2*i.val)=v i
    rw [show Odd.slot src+2*i.val=Odd.slot (src+i.val) by unfold Odd.slot; omega]
    exact (Odd.data_slot native caller _).trans (wire i)
  obtain ⟨z,publish,low,tagged⟩:=block_spec n (Odd.slot src) u v P loop.safe_end positive sep u14 u15 packed
  have close:=Block.Eval.op_addrConst (safe:=Memory.AllData P) z 17 0 publish.safe_end publish.safe_end
  refine ⟨z.putIndex 17 0,?_,low,tagged.trans u16,rfl⟩
  simpa only [fromOdd,oddTime,Nat.add_assoc] using first.seq (loop.seq (publish.seq close))

end Publish
end Recovery
end LinearProgramming
end Optimization
end OAI
