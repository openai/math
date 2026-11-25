import OAI.Optimization.LinearProgramming.Geometry.MinorDirectTail

/-! Direct, no-clear installation of the geometric scalar packet in the persistent
native service. Every register of the parked logical caller is restored. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Block RAM.Callable OracleSpec

/-- The surrounding tag dispatch selects one of the two fixed programs (tags 0 and 1).
The first request word temporarily holds the original logical scalar register three. -/
def directBody (tag : ℕ) : Block := .seq (.op (.addrConst 0 9))
  (.branch (.addrLT (Odd.slot 81) 0) (DirectCopy.head tag 2) (.seq DirectCopy.tail (DirectCopy.head tag 4)))

/-- Decode all scalar words of the original price query directly into native address
cells, using time polynomial only in the word count and their public numeric bound. -/
theorem directBody_eval (native : State ℚ) (caller : Memory ℚ) (P : ℚ → Prop) (tag sb B : ℕ) (xs : List ℕ)
    (shape : xs.length=2 ∨ 4 ≤ xs.length) (tagged : xs[0]?=some tag) (base : caller.index 80=sb)
    (len : caller.index 81=xs.length) (source : ∀ j, 1 ≤ j → j < xs.length → caller.data (sb+j)=(xs[j]?.getD 0 : ℕ))
    (zero2 : caller.data 2=0) (zero29 : caller.data 29=0) (one3 : caller.data 3=1)
    (digits : ∀ v∈xs,v ≤ B) (small : ∀ i ≤ B,P (i:ℚ)) (hn : native.memory.AllData P) (hc : caller.AllData P) :
    ∃ k ≤ xs.length*(5*B+32)+50, Eval (Memory.AllData P) (directBody tag) (Odd.memory native.memory caller) k
      (Odd.memory (MinorLog.resume native xs).memory caller) := by
  let s := Odd.memory native.memory caller
  let m := s.putIndex 0 9
  have safeS := Odd.allData native.memory caller hn hc
  have first : Eval (Memory.AllData P) (.op (.addrConst 0 9)) s 1 m := Eval.op_addrConst s 0 9 safeS safeS
  have odd (i) : m.index (Odd.slot i)=s.index (Odd.slot i) := by simp [m,show Odd.slot i≠0 by unfold Odd.slot; omega]
  have data : m.data=s.data := rfl
  have packetS : DirectCopy.ScalarPacket s sb xs :=
    ⟨by simp [s,base],by simp [s,len],fun j h1 hj => by simpa [s] using source j h1 hj,
     by simp [s,zero2],by simp [s,zero29],by simp [s,one3]⟩
  have q := packetS.frame data odd
  have preserved (i) (hp : 1 ≤ i) : m.index (2*i)=s.index (2*i) := by simp [m,show 2*i≠0 by omega]
  have mark : m.index 0=9 := by simp [m]
  rcases shape with short|large
  · obtain ⟨t,c,clock,head,hd,here,frame⟩ := DirectCopy.head_eval m P sb tag B 2 xs (by decide) (by omega) q tagged digits small first.safe_end
    have guard : (Cond.addrLT (Odd.slot 81) 0).test m=true := by
      change decide (m.index (Odd.slot 81) < m.index 0) = true
      rw [q.length, mark, short]
      decide
    have endState := installed_state native.memory caller t xs (hd.trans data)
      (fun j => (frame _ (fun i _ => by unfold Odd.slot; omega)).trans (odd j)) (fun i hi => here i (by omega))
      (fun j hj => (frame _ (fun i hi => by omega)).trans (preserved j (by omega)))
    refine ⟨1+(1+c+1),by rw [short]; omega,?_⟩
    change Eval _ _ _ _ (Odd.memory (requestedMemory native.memory xs) caller)
    rw [← endState]
    exact first.seq (Eval.branchTrue guard head)
  · obtain ⟨v,d,limit,loop,tail⟩ := DirectCopy.tail_eval m P sb B xs large q digits small first.safe_end
    have qv := q.frame tail.scalars tail.odd
    obtain ⟨t,c,clock,head,hd,here,frame⟩ := DirectCopy.head_eval v P sb tag B 4 xs (by decide) large qv tagged digits small loop.safe_end
    have guard : (Cond.addrLT (Odd.slot 81) 0).test m=false := by
      change decide (m.index (Odd.slot 81) < m.index 0) = false
      rw [q.length, mark, decide_eq_false_iff_not]
      unfold Odd.slot
      omega
    have endState := installed_state native.memory caller t xs ((hd.trans tail.scalars).trans data)
      (fun j => (frame _ (fun i _ => by unfold Odd.slot; omega)).trans ((tail.odd j).trans (odd j))) (by
        intro j hj
        by_cases h : j < 4
        · exact here j h
        · exact (frame _ (fun i hi => by omega)).trans (tail.copied j (by omega) hj))
      (fun j hj => (frame _ (fun i hi => by omega)).trans ((tail.future j hj).trans (preserved j (by omega))))
    refine ⟨1+(1+(d+c)),?_,?_⟩
    · have rest := Nat.mul_le_mul_left (xs.length-4) (show 5*B+14 ≤ 5*B+32 by omega)
      have front := Nat.mul_le_mul_left 4 (show 5*B+12 ≤ 5*B+32 by omega)
      have split : (xs.length-4)*(5*B+32)+4*(5*B+32)=xs.length*(5*B+32) := by
        rw [←Nat.add_mul,Nat.sub_add_cancel large]
      omega
    · change Eval _ _ _ _ (Odd.memory (requestedMemory native.memory xs) caller)
      rw [← endState]
      exact first.seq (Eval.branchFalse guard (loop.seq head))

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
