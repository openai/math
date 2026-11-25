import OAI.Optimization.LinearProgramming.Compression.MinorProxyInputsStep

/-! Copy one computed logarithm numerator and its symbolic flag to stable output arrays. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Registers 57, 58 and 59 are cursors into the magnitude, integer grid and flag
tapes. Register 60 counts completed cells, 61 records a symbolic value, 62 is zero,
and 63 carries the current return tag. Register 86 points to the shared denominator. -/
def writeAndAdvance : Block := .seq (.op (.store 58 0)) (.seq (.op (.addrStore 59 63))
  (.seq (.op (.incr 57 57)) (.seq (.op (.incr 58 58)) (.seq (.op (.incr 59 59)) (.op (.incr 60 60))))))

def committed (s : Memory K) : Memory K :=
  let write := (s.putData (s.index 58) (s.data 0)).putIndex (s.index 59) (s.index 63)
  (((write.putIndex 57 (s.index 57+1)).putIndex 58 (s.index 58+1)).putIndex 59 (s.index 59+1)).putIndex 60 (s.index 60+1)

theorem writeAndAdvance_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P) (hh : 64≤s.index 59) :
    Block.Eval (Memory.AllData P) writeAndAdvance s 6 (committed s) := by
  let a := s.putData (s.index 58) (s.data 0)
  let b := a.putIndex (s.index 59) (s.index 63)
  let c := b.putIndex 57 (s.index 57+1)
  let d := c.putIndex 58 (s.index 58+1)
  let e := d.putIndex 59 (s.index 59+1)
  have ha : a.AllData P := hs.putData _ (hs 0)
  have e1 := Block.Eval.op_store (safe := Memory.AllData P) s 58 0 hs ha
  have e2 : Block.Eval (Memory.AllData P) (.op (.addrStore 59 63)) a 1 b :=
    Block.Eval.op_addrStore _ _ _ ha ha
  have h57 : b.index 57=s.index 57 := by simp [b,a,show 57≠s.index 59 by omega]
  have h58 : c.index 58=s.index 58 := by simp [c,b,a,show 58≠s.index 59 by omega]
  have h59 : d.index 59=s.index 59 := by simp [d,c,b,a,show 59≠s.index 59 by omega]
  have h60 : e.index 60=s.index 60 := by simp [e,d,c,b,a,show 60≠s.index 59 by omega]
  have e3 : Block.Eval (Memory.AllData P) (.op (.incr 57 57)) b 1 c := by
    simpa only [h57] using Block.Eval.op_incr (safe := Memory.AllData P) b 57 57 ha ha
  have e4 : Block.Eval (Memory.AllData P) (.op (.incr 58 58)) c 1 d := by
    simpa only [h58] using Block.Eval.op_incr (safe := Memory.AllData P) c 58 58 ha ha
  have e5 : Block.Eval (Memory.AllData P) (.op (.incr 59 59)) d 1 e := by
    simpa only [h59] using Block.Eval.op_incr (safe := Memory.AllData P) d 59 59 ha ha
  have e6 : Block.Eval (Memory.AllData P) (.op (.incr 60 60)) e 1 (committed s) := by
    change Block.Eval _ _ e 1 (e.putIndex 60 (s.index 60+1))
    simpa only [h60] using Block.Eval.op_incr (safe := Memory.AllData P) e 60 60 ha ha
  exact e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))

structure StoreResult (s t : Memory K) (word : K) (tag anyFlag : ℕ) : Prop where
  grid : t.data (s.index 58)=word
  flag : t.index (s.index 59)=tag
  any : t.index 61=anyFlag
  readPtr : t.index 57=s.index 57+1
  gridPtr : t.index 58=s.index 58+1
  flagPtr : t.index 59=s.index 59+1
  counter : t.index 60=s.index 60+1
  scalarFrame : ∀ j, 2≤j → j≠s.index 58 → t.data j=s.data j
  indexFrame : ∀ j, (j<57 ∨ 62≤j) → j≠s.index 59 → t.index j=s.index j

/-- On an ordinary result, multiply the dyadic by the shared positive grid
denominator. A symbolic result supplies the integer zero and raises the global flag. -/
def finish : Block := .seq (.branch (.addrLT 62 63)
  (.seq (.op (.const 0 0)) (.op (.addrConst 61 1)))
  (.seq (.op (.load 1 86)) (.op (.mul 0 0 1)))) writeAndAdvance

theorem finish_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P) (tag : ℕ)
    (htag : s.index 63=tag) (hzero : s.index 62=0) (hh : 64≤s.index 59)
    (hP : P (if tag=0 then s.data 0*s.data (s.index 86) else 0)) :
    ∃ t k, k≤10 ∧ Block.Eval (Memory.AllData P) finish s k t ∧
      StoreResult s t (if tag=0 then s.data 0*s.data (s.index 86) else 0) tag
        (if tag=0 then s.index 61 else 1) := by
  let word := if tag=0 then s.data 0*s.data (s.index 86) else 0
  let w := if tag=0 then (s.putData 1 (s.data (s.index 86))).putData 0 word
    else (s.putData 0 word).putIndex 61 1
  have hw0 : w.data 0=word := by by_cases h : tag=0 <;> simp [w,h]
  have wf (j : ℕ) (hj : 2≤j) : w.data j=s.data j := by
    by_cases h : tag=0 <;> simp [w,h,show j≠0 by omega,show j≠1 by omega]
  have wi (j : ℕ) (hj : j≠61) : w.index j=s.index j := by by_cases h : tag=0 <;> simp [w,h,hj]
  have w61 : w.index 61=(if tag=0 then s.index 61 else 1) := by by_cases h : tag=0 <;> simp [w,h]
  have stage : ∃ k≤4, Block.Eval (Memory.AllData P) (.branch (.addrLT 62 63)
      (.seq (.op (.const 0 0)) (.op (.addrConst 61 1))) (.seq (.op (.load 1 86)) (.op (.mul 0 0 1)))) s k w := by
    by_cases h : tag=0
    · have no : (Cond.addrLT 62 63).test s=false := by simp [Cond.test,hzero,htag,h]
      let a := s.putData 1 (s.data (s.index 86))
      have ha : a.AllData P := hs.putData _ (hs _)
      have e1 := Block.Eval.op_load (safe := Memory.AllData P) s 1 86 hs ha
      have row : a.data 0*a.data 1=word := by simp [a,word,h]
      have hw : (a.putData 0 (a.data 0*a.data 1)).AllData P := ha.putData _ (row ▸ hP)
      have e2 := Block.Eval.op_mul (safe := Memory.AllData P) a 0 0 1 ha hw
      refine ⟨3,by decide,?_⟩
      simpa only [w,ite_eq_left h,row] using Block.Eval.branchFalse
        (a := .seq (.op (.const 0 0)) (.op (.addrConst 61 1))) no (e1.seq e2)
    · have yes : (Cond.addrLT 62 63).test s=true := by simp [Cond.test,hzero,htag,Nat.pos_of_ne_zero h]
      have h0 : P 0 := by simpa [h] using hP
      let a := s.putData 0 0
      have ha : a.AllData P := hs.putData 0 h0
      have e1 : Block.Eval (Memory.AllData P) (.op (.const 0 0)) s 1 a := by
        simpa [a] using Block.Eval.op_const s 0 0 hs (by simpa [a] using ha)
      have e2 := Block.Eval.op_addrConst (safe := Memory.AllData P) a 61 1 ha ha
      refine ⟨4,by decide,?_⟩
      simpa [w,word,h,a] using Block.Eval.branchTrue (b := .seq (.op (.load 1 86)) (.op (.mul 0 0 1))) yes (e1.seq e2)
  obtain ⟨k,hk,run⟩ := stage
  have w59 := wi 59 (by decide)
  have hh' : 64≤w.index 59 := w59 ▸ hh
  have post := writeAndAdvance_eval P w run.safe_end hh'
  refine ⟨committed w,_,by omega,run.seq post,?_⟩
  have h61 : 61≠w.index 59 := by omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [committed,wi 58 (by decide),hw0,word]
  · simp [committed,w59,show s.index 59≠57 by omega,show s.index 59≠58 by omega,
      show s.index 59≠59 by omega,show s.index 59≠60 by omega,wi 63 (by decide),htag]
  · simp [committed,h61,w61]
  · simp [committed,wi 57 (by decide)]
  · simp [committed,wi 58 (by decide)]
  · simp [committed,w59]
  · simp [committed,wi 60 (by decide)]
  · intro j hj ne
    simp [committed,wi 58 (by decide),ne,wf j hj]
  · intro j hj ne
    simp [committed,w59,ne,show j≠57 by omega,show j≠58 by omega,show j≠59 by omega,
      show j≠60 by omega,wi j (by omega)]

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
