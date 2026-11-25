import OAI.Optimization.LinearProgramming.RAM.CallableBootOps

/-! Build the encoded odd address words immediately beyond the cap. The first nine
old input words were saved before borrowing the low registers. Later words are read
directly from their original contiguous positions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

private def readDim : Block := .branch (.addrLT 6 1)
  (.branch (.addrLT 6 8) (.op (.addrLoad 9 3)) (.op (.addrLoad 9 5)))
  (.op (.addrConst 9 0))

private def setup : List AddressOp := [.incr 3 0,.set 4 1,.set 5 3,.set 6 0,.incr 7 0,.set 8 9]
private def writeOps : List AddressOp := [.store 3 10,.incr 3 3,.incr 4 4,.incr 4 4,.incr 5 5,.incr 6 6]
private def encodeOne : Block := .seq readDim (.seq encodeBlock (program writeOps))
def fillBlock : Block := .seq (program setup) (.loop (.addrLT 4 7) encodeOne)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem readDim_spec (P : K → Prop) (s : Memory K) (n i x : ℕ) (hs : s.AllData P)
    (hn : s.index 1=n) (hi : s.index 6=i) (h9 : s.index 8=9)
    (hl : i < n → i < 9 → s.index (s.index 3)=x) (hh : i < n → 9 ≤ i → s.index (s.index 5)=x)
    (hz : n ≤ i → x=0) : ∃ k ≤ 5, Eval (Memory.AllData P) readDim s k (s.putIndex 9 x) := by
  unfold readDim
  by_cases live : i < n
  · have test : (Cond.addrLT 6 1).test s=true := by simp [Cond.test,hi,hn,live]
    by_cases near : i < 9
    · have nearTest : (Cond.addrLT 6 8).test s=true := by simp [Cond.test,hi,h9,near]
      have primitive : Eval (Memory.AllData P) (.op (.addrLoad 9 3)) s 1 (s.putIndex 9 x) := by
        simpa only [hl live near] using Eval.op_addrLoad (safe:=Memory.AllData P) s 9 3 hs hs
      have select := Eval.branchTrue (b:=.op (.addrLoad 9 5)) nearTest primitive
      exact ⟨5,by decide,Eval.branchTrue (b:=.op (.addrConst 9 0)) test select⟩
    · have farTest : (Cond.addrLT 6 8).test s=false := by simp [Cond.test,hi,h9,near]
      have primitive : Eval (Memory.AllData P) (.op (.addrLoad 9 5)) s 1 (s.putIndex 9 x) := by
        simpa only [hh live (by omega)] using Eval.op_addrLoad (safe:=Memory.AllData P) s 9 5 hs hs
      have select := Eval.branchFalse (a:=.op (.addrLoad 9 3)) farTest primitive
      exact ⟨4,by decide,Eval.branchTrue (b:=.op (.addrConst 9 0)) test select⟩
  · have missing : (Cond.addrLT 6 1).test s=false := by simp [Cond.test,hi,hn,live]
    have primitive : Eval (Memory.AllData P) (.op (.addrConst 9 0)) s 1 (s.putIndex 9 x) := by
      rw [hz (by omega)]
      exact Eval.op_addrConst s 9 0 hs hs
    exact ⟨2,by decide,Eval.branchFalse
      (a:=.branch (.addrLT 6 8) (.op (.addrLoad 9 3)) (.op (.addrLoad 9 5))) missing primitive⟩

private structure Written (s t : Memory K) (cap i val : ℕ) : Prop where
  data : t.data=s.data
  high : t.index (cap+1+i)=val
  p3 : t.index 3=cap+1+(i+1)
  p4 : t.index 4=2*(i+1)+1
  p5 : t.index 5=3+(i+1)
  p6 : t.index 6=i+1
  frame : ∀ r, r≠3 → r≠4 → r≠5 → r≠6 → r≠cap+1+i → t.index r=s.index r

private theorem write_spec (P : K → Prop) (s : Memory K) (cap i v : ℕ) (hc : 12 ≤ cap)
    (hs : s.AllData P) (p3 : s.index 3=cap+1+i) (p4 : s.index 4=2*i+1)
    (p5 : s.index 5=3+i) (p6 : s.index 6=i) (p10 : s.index 10=v) :
    ∃ t, Eval (Memory.AllData P) (program writeOps) s 6 t ∧ Written s t cap i v := by
  let t := applyOps writeOps s
  refine ⟨t,ops_spec P writeOps s hs,ops_data ..,?_,?_,?_,?_,?_,?_⟩
  all_goals try (intro r h3 h4 h5 h6 hh)
  all_goals simp (disch := omega) [t,writeOps,applyOps,AddressOp.apply,p3,p4,p5,p6,p10]
  all_goals omega

private structure FillAt (P : K → Prop) (s : Memory K) (cap n : ℕ) (f : ℕ→ℕ)
    (i : ℕ) (t : Memory K) : Prop where
  safe : t.AllData P
  data : t.data=s.data
  capReg : t.index 0=cap
  sizeReg : t.index 1=n
  highPtr : t.index 3=cap+1+i
  oddPtr : t.index 4=2*i+1
  source : t.index 5=3+i
  count : t.index 6=i
  upper : t.index 7=cap+1
  nine : t.index 8=9
  words : ∀ j < i, t.index (cap+1+j)=2*f j+1
  frame : ∀ r, 11 < r → (r < cap+1 ∨ cap+1+i ≤ r) → t.index r=s.index r

/-- The high buffer has one word per odd physical address at or below the cap. -/
theorem fillBlock_spec (P : K → Prop) (s : Memory K) (cap n B : ℕ) (f : ℕ→ℕ)
    (hs : s.AllData P) (hc : 64 ≤ cap) (hncap : 2*n+4 ≤ cap)
    (h0 : s.index 0=cap) (h1 : s.index 1=n)
    (low : ∀ i < n, i < 9 → s.index (cap+1+i)=f i)
    (high : ∀ i, 9 ≤ i → i < n → s.index (3+i)=f i)
    (zero : ∀ i, n ≤ i → f i=0) (bound : ∀ i, f i ≤ B) :
    ∃ t k, k ≤ 6+((cap+1)/2)*(5*B+16)+1 ∧ Eval (Memory.AllData P) fillBlock s k t ∧
      t.data=s.data ∧ t.index 0=cap ∧
      (∀ j < (cap+1)/2, t.index (cap+1+j)=2*f j+1) ∧
      ∀ r, 11 < r → (r < cap+1 ∨ cap+1+(cap+1)/2 ≤ r) → t.index r=s.index r := by
  let a := applyOps setup s
  have ea := ops_spec P setup s hs
  let I := FillAt P s cap n f
  have init : I 0 a := by
    refine ⟨ea.safe_end,ops_data ..,?_,?_,?_,?_,?_,?_,?_,?_,fun j h => (Nat.not_lt_zero _ h).elim,?_⟩
    all_goals try (intro r hr _)
    all_goals simp (disch := omega) [a,setup,applyOps,AddressOp.apply,h0,h1]
  obtain ⟨t,k,hk,run,out⟩ := Eval.loop_invariant (safe:=Memory.AllData P)
    (c:=.addrLT 4 7) (body:=encodeOne) I a ((cap+1)/2) (5*B+14) init
    (by
      intro i hi u h
      have guard : (Cond.addrLT 4 7).test u=true := by
        simp only [Cond.test,decide_eq_true_eq,h.oddPtr,h.upper]
        omega
      obtain ⟨kr,hkr,rd⟩ := readDim_spec P u n i (f i) h.safe h.sizeReg h.count h.nine
        (fun hn hl => by rw [h.highPtr,h.frame _ (by omega) (.inr le_rfl),low i hn hl])
        (fun hn hh => by rw [h.source,h.frame _ (by omega) (.inl (by omega)),high i hh hn])
        (zero i)
      let v := u.putIndex 9 (f i)
      obtain ⟨w,enc,wd,wval,wfr⟩ := encode_spec P v rd.safe_end
      have wf (r : ℕ) (h9 : r≠9) (h10 : r≠10) (h11 : r≠11) : w.index r=u.index r :=
        (wfr r h10 h11).trans (Memory.putIndex_ne u h9 _)
      obtain ⟨z,put,zf⟩ := write_spec P w cap i (2*f i+1) (by omega) enc.safe_end
        ((wf 3 (by decide) (by decide) (by decide)).trans h.highPtr)
        ((wf 4 (by decide) (by decide) (by decide)).trans h.oddPtr)
        ((wf 5 (by decide) (by decide) (by decide)).trans h.source)
        ((wf 6 (by decide) (by decide) (by decide)).trans h.count) (by simpa [v] using wval)
      have frame (r : ℕ) (h3 : r≠3) (h4 : r≠4) (h5 : r≠5) (h6 : r≠6)
          (h9 : r≠9) (h10 : r≠10) (h11 : r≠11) (hh : r≠cap+1+i) :
          z.index r=u.index r := (zf.frame _ h3 h4 h5 h6 hh).trans (wf _ h9 h10 h11)
      have one := rd.seq (enc.seq put)
      refine ⟨guard,z,kr+(5*f i+3+6),by have := bound i; omega,?_,put.safe_end,
        zf.data.trans (wd.trans h.data),?_,?_,zf.p3,zf.p4,zf.p5,zf.p6,?_,?_,?_,?_⟩
      · simpa [v,encodeOne] using one
      · exact (frame 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans h.capReg
      · exact (frame 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans h.sizeReg
      · exact (frame 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans h.upper
      · exact (frame 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans h.nine
      · intro j hj
        by_cases eq : j=i
        · simpa [eq] using zf.high
        · exact (frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (h.words j (by omega))
      · intro r hr loc
        exact (frame _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (h.frame r hr (by omega)))
    (by
      intro u h
      refine ⟨?_,h.safe⟩
      simp only [Cond.test,decide_eq_false_iff_not,h.oddPtr,h.upper]
      omega)
  refine ⟨t,6+k,?_,ea.seq run,out.data,out.capReg,out.words,out.frame⟩
  rw [show 5*B+14+2=5*B+16 by omega] at hk
  omega

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
