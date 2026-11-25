import OAI.Optimization.LinearProgramming.Recovery.PublishOdd
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.RAM.CallableControl

/-! The dual output is the tail of the computed normalized nonnegative vector.
This branch copies the actual stored coordinates into the public tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace DualOutput
open RAM RAM.Callable

private def ops : List Instr := [.incr 210 212,.addrCopy 211 28]
def program : Fragment:=.seq (Odd.leaf (Block.straight ops)) (.ofBlock (Publish.fromOdd 1))

theorem program_run {m : ℕ} (native caller : Memory ℚ) (w : Fin (m+1)→ℚ) (atW H : ℕ)
    (rows : caller.index 28=m) (src : caller.index 212=atW) (high : m ≤ atW) (hm : 0<m)
    (actual : ∀j : Fin (m+1),caller.data (atW+j.val)=w j)
    (hs : native.AllData (fun q=>ratBits q ≤ H)) (hc : caller.AllData (fun q=>ratBits q ≤ H)) :
    ∃ z,program.Run (fun q=>ratBits q ≤ H) (Odd.memory native caller) (8+Publish.oddTime m) z ∧
      (∀i : Fin m,z.data i.val=(Fin.tail w) i) ∧ z.index 16=1 ∧ z.index 17=0 := by
  let t:=(caller.putIndex 210 (atW+1)).putIndex 211 m
  have run : Block.Eval (Memory.AllData (fun q=>ratBits q ≤ H)) (Block.straight ops) caller 2 t := by
    have eval := BitRAM.IndexScript.correct ops (by simp [ops,BitRAM.IndexScript.allowed]) caller
      (P := fun q : ℚ => ratBits q ≤ H) hc
    unfold Tape.Good at eval
    unfold Memory.AllData
    simpa [ops,t,BitRAM.IndexScript.run,BitRAM.IndexScript.update,Memory.putIndex,src,rows] using eval
  have out : ∀i : Fin m,t.data (atW+1+i.val)=Fin.tail w i:=by
    intro i
    have eq : atW+1+i.val=atW+i.succ.val:=by change atW+1+i.val=atW+(i.val+1);omega
    rw [eq];exact actual i.succ
  obtain ⟨z,finish,value,one,zero⟩:=Publish.fromOdd_spec 1 m (atW+1) native t (Fin.tail w) (fun q=>ratBits q ≤ H)
    hs run.safe_end hm (by unfold Odd.slot;omega) (by simp [t,Memory.putIndex]) (by simp [t,Memory.putIndex]) out
  exact ⟨z,(Odd.leaf_run _ native hs run).seq (Fragment.Run.ofBlock finish),value,one,zero⟩

end DualOutput
end Recovery
end LinearProgramming
end Optimization
end OAI
