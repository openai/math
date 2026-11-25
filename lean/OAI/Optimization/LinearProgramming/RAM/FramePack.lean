import OAI.Optimization.LinearProgramming.RAM.FrameClear
import OAI.Optimization.LinearProgramming.RAM.CallMemory
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Prepare an isolated call from staged flat input and a separate caller save area.
The callee sees its exact input and zeros in every other scalar register. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

/-- The two scan pointers and the loop counter are odd address registers; scalar 1 is the
scratch value. The destination is one parity class, indexed by `first + 2*j`. -/
def scatter (srcReg lenReg first : Nat) : Block :=
  .seq (.op (.addrCopy 31 srcReg)) (.seq (.op (.addrConst 7 first))
    (StrideCopy.block false 31 7 35 lenReg 1 1 2))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- A flat source above the destination remains intact during the scan. The result has
an explicit scalar frame, including when the two convex hulls contain unused cells. -/
theorem scatter_correct (s : Memory K) (srcReg lenReg first n : Nat)
    (hs : Good P s) (hlen : s.index lenReg = n)
    (hregs : [31, 7, 35, lenReg].Nodup)
    (hsrc : 2 ≤ s.index srcReg) (hsep : first+2*n ≤ s.index srcReg)
    (hdst : ∀ j < n, first + 2*j ≠ 1) :
    ∃ t, Eval (Good P) (scatter srcReg lenReg first) s (8*n+4) t ∧
      (∀ j < n, t.data (first+2*j) = s.data (s.index srcReg+j)) ∧
      (∀ a, a≠1 → (∀ j < n, a ≠ first+2*j) → t.data a = s.data a) ∧
      t.index 7 = first+2*n ∧
      ∀ r, r≠31 → r≠7 → r≠35 → t.index r = s.index r := by
  let a := s.putIndex 31 (s.index srcReg)
  let b := a.putIndex 7 first
  have setA : Eval (Good P) (.op (.addrCopy 31 srcReg)) s 1 a := eval_copyI s hs _ _
  have setB : Eval (Good P) (.op (.addrConst 7 first)) a 1 b := eval_constI a hs _ _
  have l31 : lenReg ≠ 31 := by rintro rfl; simp at hregs
  have l7 : lenReg ≠ 7 := by rintro rfl; simp at hregs
  have bl : b.index lenReg = n := by simpa [b,a,l7,l31] using hlen
  have bs : b.index 31 = s.index srcReg := by simp [b,a]
  have bd : b.index 7 = first := by simp [b]
  obtain ⟨t,run,values,preserve,_,dst,_,indices⟩ := StrideCopy.block_correct P b false
    31 7 35 lenReg 1 1 2 n hs bl hregs (by decide) (by simp)
    (fun j _ => by simp [StrideCopy.address_forward,bs]; omega)
    (fun j hj => by simpa [StrideCopy.address_forward,bd] using hdst j hj)
    (fun i j hij hj => StrideCopy.forward_separated (by decide) (by decide)
      (Or.inr (by simpa [bs,bd] using hsep)) (lt_trans hij hj) hj)
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8*n+4 = 1+(1+(n*(1+2+5)+2)) by omega]
    exact setA.seq (setB.seq run)
  · intro j hj; simpa [StrideCopy.address_forward,bs,bd,b,a] using values j hj
  · intro i h1 hne
    have h := preserve i h1 (by simpa [StrideCopy.address_forward,bd] using hne)
    simpa [b,a] using h
  · simpa [StrideCopy.address_forward,bd] using dst
  · intro r h31 h7 h35
    simpa [b,a,h7,h31] using indices r h31 h7 h35

/-- `13,15` hold the start and length of the callee input, `17,19` describe the saved
caller data. `21` bounds the potentially nonzero part of the original tape. The saved
array starts at scalar register 3 so scalar 1 remains available as a scratch register. -/
def prepareScalars : Block :=
  .seq (scatter 17 19 3) (.seq (scatter 13 15 0)
    (.seq (.op (.const 1 0)) (.seq (.op (.addrConst 3 0))
      (.seq (.op (.addrCopy 5 21)) (clearWindow true)))))

/-- The staged input and saved array can overlap each other, as in the first call of the
optimization reduction. Both sources lie above the destinations of the copying passes. -/
theorem prepareScalars_correct_framed (s : Memory K) (vs vn fs fn limit : Nat)
    (hs : Good P s) (hz : P 0) (hv : s.index 13=vs) (hn : s.index 15=vn)
    (hf : s.index 17=fs) (hfn : s.index 19=fn) (hlim : s.index 21=limit)
    (hvs : 3+2*(vn+fn) ≤ vs) (hfs : 3+2*(vn+fn) ≤ fs)
    (htail : ∀ i, limit ≤ i → s.data (2*i)=0) :
    ∃ t, Eval (Good P) prepareScalars s (8*(vn+fn)+6*limit+12) t ∧
      (∀ i, t.data (2*i) = if i<vn then s.data (vs+i) else 0) ∧
      (∀ i < fn, t.data (3+2*i) = s.data (fs+i)) ∧
      (∀ r, r≠3 → r≠5 → r≠7 → r≠31 → r≠35 → t.index r = s.index r) ∧
      t.index 3=0 ∧ t.data 1=0 ∧
      ∀ q, q%2=1 → q≠1 → 3+2*fn ≤ q → t.data q=s.data q := by
  obtain ⟨f, rf, fsave, fdata, _, fix⟩ := scatter_correct s 17 19 3 fn hs hfn (by decide)
    (by omega) (by omega) (fun _ _ => by omega)
  have f13 : f.index 13=vs := (fix 13 (by decide) (by decide) (by decide)).trans hv
  have f15 : f.index 15=vn := (fix 15 (by decide) (by decide) (by decide)).trans hn
  obtain ⟨v,rv,vargs,vdata,vptr,vix⟩ := scatter_correct f 13 15 0 vn rf.safe_end f15 (by decide)
    (by omega) (by omega) (fun _ _ => by omega)
  let z := v.putData 1 0
  let a := z.putIndex 3 0
  let b := a.putIndex 5 (a.index 21)
  have rz : Eval (Good P) (.op (.const 1 0)) v 1 z :=
    by simpa [z] using (Eval.op_const (safe := Good P) v 1 0 rv.safe_end
      (Memory.AllData.putData rv.safe_end 1 (by simpa only [Rat.cast_zero] using hz)))
  have ra : Eval (Good P) (.op (.addrConst 3 0)) z 1 a := eval_constI z rz.safe_end _ _
  have rb : Eval (Good P) (.op (.addrCopy 5 21)) a 1 b := eval_copyI a ra.safe_end _ _
  have v21 : v.index 21=limit := (vix 21 (by decide) (by decide) (by decide)).trans
    ((fix 21 (by decide) (by decide) (by decide)).trans hlim)
  have b7 : b.index 7 = 2*vn := by simpa [b,a,z] using vptr
  obtain ⟨t,rc,_,_,ci,cd⟩ := clearWindow_correct true b vn limit rb.safe_end
    (by simp [b,a]) (fun _ => by simp [b,a,z]) b7 (by simp [b,a,z,v21])
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8*(vn+fn)+6*limit+12 = (8*fn+4)+((8*vn+4)+(1+(1+(1+(6*limit+1))))) by omega]
    exact rf.seq (rv.seq (rz.seq (ra.seq (rb.seq rc))))
  · intro i
    rw [cd]
    by_cases h : i < vn
    · have read := fdata (vs+i) (by omega) (fun j hj => by omega)
      have val := vargs i h
      simp only [Nat.zero_add,f13,read] at val
      simpa [h,inEvenWindow,b,a,z,show 2*i ≠ 1 by omega,show ¬ 2*vn ≤ 2*i by omega] using val
    · by_cases near : i < vn+limit
      · have inside : inEvenWindow vn limit (2*i) := by unfold inEvenWindow; omega
        simp [inside,h]
      · have keep := vdata (2*i) (by omega) (fun j hj => by omega)
        have before := fdata (2*i) (by omega) (fun j _ => by omega)
        have far := htail i (by omega)
        simp [inEvenWindow,h,show ¬ 2*i < 2*(vn+limit) by omega,b,a,z,
          show 2*i ≠ 1 by omega,keep,before,far]
  · intro i hi
    have keep := vdata (3+2*i) (by omega) (fun j _ => by omega)
    have fval := fsave i hi
    rw [hf] at fval
    rw [cd]
    simp [inEvenWindow,b,a,z,show 3+2*i ≠ 1 by omega,keep,fval]
  · intro r h3 h5 h7 h31 h35
    rw [ci r h5 h7]
    simp [b,a,z,h3,h5,vix r h31 h7 h35,fix r h31 h7 h35]
  · rw [ci 3 (by decide) (by decide)]; simp [b,a,z]
  · rw [cd]; simp [inEvenWindow,b,a,z]

  · intro q hodd h1 hfar
    have outside : ¬inEvenWindow vn limit q := fun h => by have := h.1; omega
    have vkeep := vdata q h1 (fun j _ => by omega)
    have fkeep := fdata q h1 (fun j hj => by omega)
    rw [cd]
    simp [outside,b,a,z,h1,vkeep,fkeep]

theorem prepareScalars_correct (s : Memory K) (vs vn fs fn limit : Nat)
    (hs : Good P s) (hz : P 0) (hv : s.index 13=vs) (hn : s.index 15=vn)
    (hf : s.index 17=fs) (hfn : s.index 19=fn) (hlim : s.index 21=limit)
    (hvs : 3+2*(vn+fn) ≤ vs) (hfs : 3+2*(vn+fn) ≤ fs)
    (htail : ∀ i, limit ≤ i → s.data (2*i)=0) :
    ∃ t, Eval (Good P) prepareScalars s (8*(vn+fn)+6*limit+12) t ∧
      (∀ i, t.data (2*i) = if i<vn then s.data (vs+i) else 0) ∧
      (∀ i < fn, t.data (3+2*i) = s.data (fs+i)) ∧
      (∀ r, r≠3 → r≠5 → r≠7 → r≠31 → r≠35 → t.index r = s.index r) ∧
      t.index 3=0 ∧ t.data 1=0 := by
  obtain ⟨t,run,args,saved,idx,zeroI,zeroD,_⟩ := prepareScalars_correct_framed s vs vn fs fn limit
    hs hz hv hn hf hfn hlim hvs hfs htail
  exact ⟨t,run,args,saved,idx,zeroI,zeroD⟩

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
