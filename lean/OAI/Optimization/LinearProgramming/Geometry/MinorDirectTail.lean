import OAI.Optimization.LinearProgramming.Geometry.MinorDirectHead
import OAI.Optimization.LinearProgramming.Geometry.MinorNativeTail

/-! Decode the variable-length tail from its original scalar packet, leaving the
odd caller available throughout the execution boundary of each decoded word. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall
namespace DirectCopy

open RAM RAM.Block RAM.Callable

def tailBody : Block := .seq (decodeScalarWord 0 6) NativeCopy.advance

def tail : Block := .seq (NativeCopy.setupFrom 80) (.loop (.addrLT 4 (Odd.slot 81)) tailBody)

theorem tail_eval (m : Memory ℚ) (P : ℚ → Prop) (sb B : ℕ) (xs : List ℕ) (large : 4 ≤ xs.length)
    (packet : ScalarPacket m sb xs) (digits : ∀ v∈xs,v ≤ B) (small : ∀ i ≤ B,P (i:ℚ)) (hm : m.AllData P) :
    ∃ t c, c ≤ 12+(xs.length-4)*(5*B+14) ∧ Eval (Memory.AllData P) tail m c t ∧ NativeCopy.TailState m t sb xs xs.length := by
  obtain ⟨u,setup,start⟩ := NativeCopy.setupFrom_eval m P 80 sb xs hm packet.base
  let I (i : ℕ) (v : Memory ℚ) := NativeCopy.TailState m v sb xs (4+i)
  have eq : 4+(xs.length-4)=xs.length := by omega
  obtain ⟨t,c,hc,loop,done⟩ := Eval.loop_invariant (safe := Memory.AllData P) (c := .addrLT 4 (Odd.slot 81))
    (body := tailBody) I u (xs.length-4) (5*B+12) start (by
      intro i hi s now
      have q := packet.frame now.scalars now.odd
      have hcur : s.index 4=Odd.slot (4+i) := now.cursor
      have inRange : 4+i < xs.length := by omega
      refine ⟨by simp [Cond.test,hcur,q.length,inRange],?_⟩
      let v := xs[4+i]?.getD 0
      have hv : v ≤ B := digit_le digits _ inRange
      have safe : s.AllData P := by rw [Memory.AllData,now.scalars]; exact hm
      have token : s.data (s.index 0)=(v:ℚ) := by rw [now.source]; exact q.token _ (by omega) inRange
      have decode := decodeScalarWord_eval s P 0 6 v safe token q.zero2 q.zero29 q.one3 (fun j hj => small j (hj.trans hv))
      obtain ⟨w,commit,after⟩ := NativeCopy.advance_eval m s P sb (4+i) xs (by omega) now safe
      exact ⟨w,5*v+5+7,by omega,decode.seq commit,by simpa only [Nat.add_assoc] using after⟩) (by
      intro s now
      have q := packet.frame now.scalars now.odd
      have cur := now.cursor
      refine ⟨by simp [Cond.test,cur,q.length,eq],?_⟩
      rw [Memory.AllData,now.scalars]; exact hm)
  refine ⟨t,11+c,?_,setup.seq loop,?_⟩
  · rw [show 5*B+12+2=5*B+14 by omega] at hc
    omega
  · change NativeCopy.TailState m t sb xs (4+(xs.length-4)) at done
    rwa [eq] at done

end DirectCopy
end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
