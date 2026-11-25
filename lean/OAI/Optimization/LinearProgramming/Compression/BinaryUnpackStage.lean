import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackLayout

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Save the three public header words just after the even-address source interval. -/
def stageDoubledHeader : Block := .seq (.op (.addrStore 1 7)) <| .seq (.op (.incr 1 1)) <|
  .seq (.op (.addrStore 1 9)) <| .seq (.op (.incr 1 1)) <| .seq (.op (.decr 3 4)) (.op (.addrStore 1 3))

theorem stageDoubledHeader_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (pack : CountedPacket m n d sign digit) (bound : 2 ≤ n+d) (hs : sign ≤ 1) :
    ∃ t, Block.Eval (Memory.AllData P) stageDoubledHeader m 6 t ∧ StagedPacket t n d sign digit ∧ t.data=m.data := by
  let H := endOfDoubledWords n d
  have lo : 10 ≤ H := by dsimp [H,endOfDoubledWords]; omega
  let a := m.putIndex H n
  let b := a.putIndex 1 (H+1)
  let c := b.putIndex (H+1) d
  let w := c.putIndex 1 (H+2)
  let z := w.putIndex 3 sign
  let t := z.putIndex (H+2) sign
  have ptr : m.index 1=H := pack.pointer
  have pa : a.index 1=H := by simp [a,show 1 ≠ H by omega,ptr]
  have pb : b.index 9=d := by simp [b,a,show 9 ≠ H by omega,pack.denominatorWidth]
  have pb1 : b.index 1=H+1 := Memory.putIndex_same ..
  have pc : c.index 1=H+1 := (Memory.putIndex_ne b (show 1 ≠ H+1 by omega) d).trans pb1
  have pw : w.index 4=2*sign := by simp [w,c,b,a,show 4 ≠ H+1 by omega,show 4 ≠ H by omega,pack.negative]
  have sub : w.index 4-1=sign := by rw [pw]; omega
  have s1 : Block.Eval (Memory.AllData P) (.op (.addrStore 1 7)) m 1 a := by
    simpa only [a,ptr,pack.numeratorWidth] using Block.Eval.op_addrStore m 1 7 safe (safe.putIndex _ _)
  have s2 : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) a 1 b := by
    simpa only [b,pa] using Block.Eval.op_incr a 1 1 s1.safe_end (s1.safe_end.putIndex _ _)
  have s3 : Block.Eval (Memory.AllData P) (.op (.addrStore 1 9)) b 1 c := by
    simpa only [c,pb1,pb] using Block.Eval.op_addrStore b 1 9 s2.safe_end (s2.safe_end.putIndex _ _)
  have s4 : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) c 1 w := by
    simpa only [w,pc] using Block.Eval.op_incr c 1 1 s3.safe_end (s3.safe_end.putIndex _ _)
  have s5 : Block.Eval (Memory.AllData P) (.op (.decr 3 4)) w 1 z := by
    simpa only [z,sub] using Block.Eval.op_decr w 3 4 s4.safe_end (s4.safe_end.putIndex _ _)
  have pz : z.index 1=H+2 := by simp [z,w]
  have s6 : Block.Eval (Memory.AllData P) (.op (.addrStore 1 3)) z 1 t := by
    simpa only [t,pz,show z.index 3=sign from Memory.putIndex_same ..] using Block.Eval.op_addrStore z 1 3 s5.safe_end (s5.safe_end.putIndex _ _)
  refine ⟨t,s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6)))),⟨?_,?_,?_,pack.count,?_⟩,rfl⟩
  · change t.index H=n
    calc
      _ = z.index H := Memory.putIndex_ne _ (by omega) _
      _ = w.index H := Memory.putIndex_ne _ (by omega) _
      _ = c.index H := Memory.putIndex_ne _ (by omega) _
      _ = b.index H := Memory.putIndex_ne _ (by omega) _
      _ = a.index H := Memory.putIndex_ne _ (by omega) _
      _ = n := Memory.putIndex_same ..
  · change t.index (H+1)=d
    calc
      _ = z.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = w.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = c.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = d := Memory.putIndex_same ..
  · exact Memory.putIndex_same ..
  · intro i hi
    have lt : 6+2*i < H := by dsimp [H,endOfDoubledWords]; omega
    simpa [t,z,w,c,b,a,show 6+2*i ≠ H+2 by omega,show 6+2*i ≠ 3 by omega,
      show 6+2*i ≠ 1 by omega,show 6+2*i ≠ H+1 by omega,lt.ne] using pack.words i hi

end Compression
end LinearProgramming
end Optimization
end OAI
