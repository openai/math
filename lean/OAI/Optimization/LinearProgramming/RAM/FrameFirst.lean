import OAI.Optimization.LinearProgramming.RAM.FrameFirstHeader
import OAI.Optimization.LinearProgramming.RAM.FrameReady

/-! Normal input of the first feasibility call in the two-call optimization reduction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

/-- The original scalar input starts at register zero. The forward copy saves it before
the callee receives its own writable copy. -/
def firstPrelude (p : Program) (C E : Nat) : Block := .seq (firstHeaderBlock p C E)
  (.seq (PrimalDual.copyWindow false) prepareCallInputs)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem start_index_le (m d : Nat) (w : List K) (i : Nat) :
    (start [m,d] w).index i ≤ m+d := by
  change (([m,d] : List Nat)[i]?).getD 0 ≤ m+d
  cases hw : ([m,d] : List Nat)[i]? with
  | none => exact Nat.zero_le _
  | some x =>
    have h := List.mem_of_getElem? hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem start_index_zero (m d : Nat) (w : List K) {i : Nat} (hi : 2 ≤ i) :
    (start [m,d] w).index i = 0 := by simp [start, List.getElem?_eq_none (by simpa using hi : [m,d].length ≤ i)]

/-- Everything a continuation needs to inspect the return and to choose fresh memory
for the second system. The scalar/index tails describe actual cells, including cells
outside either output window. -/
structure FirstReady (p : Program) (C E m d : Nat) (xs obj : List K) (t : Memory K) : Prop where
  data : ∀ i, t.data (2*i) = (start [m,d] xs).data i
  index : ∀ i, t.index (2*i) = 2*(start [m,d] xs).index i
  saved : ∀ i < (xs++obj).length, t.data (3+2*i) = (start [m,d] (xs++obj)).data i
  savedRows : t.index 9 = m
  savedCols : t.index 11 = d
  savedLimit : t.index 21 = firstLimit p C E m d
  oddDataTail : ∀ j, firstLimit p C E m d < j → t.data (2*j+1) = 0
  oddIndexTail : ∀ j, firstLimit p C E m d < j → t.index (2*j+1) = 0

noncomputable def firstCost (p : Program) (C E m d : Nat) : Nat :=
  (HeaderPlan.budget (firstHeaders p C E)).eval (m+d) + 4 +
  (7*optimizationLength m d+1) + (8*(primalLength m d+optimizationLength m d)+
    12*firstLimit p C E m d+4*m+4*d+21)

/-- Run the complete frame setup on the ordinary unshifted rational or field tape. -/
theorem firstPrelude_correct (p : Program) (C E m d : Nat) (xs obj : List K)
    (hx : xs.length = primalLength m d) (hy : obj.length = d) (hz : P 0)
    (hs : Good P (start [m,d] (xs++obj)).memory) :
    ∃ t k, Eval (Good P) (firstPrelude p C E) (start [m,d] (xs++obj)).memory k t ∧
      k ≤ firstCost p C E m d ∧ FirstReady p C E m d xs obj t := by
  let w := xs++obj
  let m₀ := (start [m,d] w).memory
  let L := optimizationLength m d
  let H := firstSource m d
  let B := firstLimit p C E m d
  have hL : w.length = L := by simp [w,L,optimizationLength,hx,hy]
  have hpart : xs.length ≤ L := by simp [L,optimizationLength,hx]
  have hH : 3+2*(xs.length+L) = H := by simp [H,firstSource,L,hx]
  have bcap : firstStatic p C E ≤ B := le_max_right _ _
  have blarge : H+L+100 ≤ B := by
    apply le_trans _ (le_max_left _ _ : rawLimit p C E m d ≤ B)
    change H+L+100 ≤ H+L+100+_+_; omega
  obtain ⟨u,k,rh,hk,udan,ptr,idxFr⟩ := firstHeaderBlock_correct p C E m d m₀ hs rfl rfl
    (fun i => start_index_le m d w i)
  have hsep : L ≤ H := by omega
  obtain ⟨v,copy,values,dataFr,idx⟩ := PrimalDual.copyWindow_correct false L 0 H u rh.safe_end
    ptr.source ptr.destination ptr.count ptr.zero (Or.inl (by omega)) (by simp; omega)
  have rows : v.index 9 = m := (idx 9 (by decide)).trans ptr.rows
  have cols : v.index 11 = d := (idx 11 (by decide)).trans ptr.cols
  have dv : v.index 13 = H := (idx 13 (by decide)).trans ptr.primalSource
  have dn : v.index 15 = xs.length := (idx 15 (by decide)).trans (ptr.primalWords.trans hx.symm)
  have df : v.index 17 = H := (idx 17 (by decide)).trans ptr.savedSource
  have dL : v.index 19 = L := (idx 19 (by decide)).trans ptr.savedWords
  have dB : v.index 21 = B := (idx 21 (by decide)).trans ptr.limit
  have farData (q : Nat) (hfar : B ≤ q) : v.data q = 0 := by
    rw [dataFr q (by omega) (Or.inr (by omega)),udan]
    change (w[q]?).getD 0 = 0
    simp [List.getElem?_eq_none (by omega : w.length ≤ q)]
  have farIndex (q : Nat) (hfar : B ≤ q) : v.index q = 0 := by
    rw [idx q (by omega),idxFr q (bcap.trans hfar)]
    exact start_index_zero m d w (by omega)
  have savedValues (i : Nat) (hi : i < L) : v.data (H+i) = m₀.data i := by
    simpa [udan] using values i hi
  have read (i : Nat) (hi : i < xs.length) : v.data (H+i) = (start [m,d] xs).data i := by
    rw [savedValues i (by omega)]
    change (w[i]?).getD 0 = (xs[i]?).getD 0
    rw [show w[i]? = xs[i]? from List.getElem?_append_left hi]
  obtain ⟨t,rf,rd,ri,rs,rtail,rif⟩ := prepareCallInputs_correct v m d H H L B xs copy.safe_end
    hz rows cols dv dn df dL dB hH.le hH.le (fun i hi => farData _ (by omega))
    (fun i hi => farIndex _ (by omega)) read
  refine ⟨t,_,rh.seq (copy.seq rf),?_,rd,ri,?_,?_,?_,?_,?_,?_⟩
  · simp only [firstCost,← hx] at *
    omega
  · intro i hi
    have h : i < L := by simpa [w,hL] using hi
    exact (rs i h).trans (savedValues i h)
  · exact (rif 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rows
  · exact (rif 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cols
  · exact (rif 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans dB
  · intro j hj
    change B < j at hj
    exact (rtail (2*j+1) (by omega) (by omega) (by omega)).trans (farData _ (by omega))
  · intro j hj
    change B < j at hj
    exact (rif (2*j+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (farIndex _ (by omega))

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
