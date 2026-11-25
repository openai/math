import OAI.Optimization.LinearProgramming.RAM.Array

/-! An exact-cost uniform gather/scatter routine using only unit pointer motion. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace StrideCopy

open Block

/-- The initial pointer addresses the first cell visited, including on a backward scan. -/
def move (back : Bool) (base count : Nat) : Nat := if back then base-count else base+count

def address (back : Bool) (base stride j : Nat) : Nat := move back base (stride*j)

private def advance (back : Bool) (ptr stride : Nat) : Block :=
  Block.straight (List.replicate stride (if back then .decr ptr ptr else .incr ptr ptr))

private theorem move_add (b : Bool) (a j k : Nat) : move b (move b a j) k = move b a (j+k) := by
  cases b <;> simp [move,Nat.add_assoc,Nat.sub_sub]

private theorem advance_address (b : Bool) (a stride j : Nat) :
    move b (address b a stride j) stride = address b a stride (j+1) := by
  simp [address,Nat.mul_succ,move_add]

@[simp] theorem address_zero (b : Bool) (a stride : Nat) : address b a stride 0 = a := by
  cases b <;> simp [address,move]

private theorem address_ne {b : Bool} {a stride n j k : Nat} (hstride : 0<stride)
    (hroom : b = true → stride*(n-1) ≤ a) (hj : j<k) (hk : k<n) :
    address b a stride j ≠ address b a stride k := by
  have strict := Nat.mul_lt_mul_of_pos_left hj hstride
  cases b with
  | false => simp [address,move,strict.ne]
  | true =>
    have fits := (Nat.mul_le_mul_left stride (by omega : k≤n-1)).trans (hroom rfl)
    simp only [address,move,ite_true]
    omega

private theorem advance_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (b : Bool) (ptr stride : Nat) (hm : m.AllData P) :
    ∃ t, Eval (Memory.AllData P) (advance b ptr stride) m stride t ∧
      t.data=m.data ∧ t.index ptr=move b (m.index ptr) stride ∧
      ∀ r, r≠ptr → t.index r=m.index r := by
  induction stride generalizing m with
  | zero =>
    exact ⟨m,.skip hm,rfl,by cases b <;> simp [move],fun _ _ => rfl⟩
  | succ stride ih =>
    let u := m.putIndex ptr (move b (m.index ptr) 1)
    have hu : u.AllData P := hm
    have one : Eval (Memory.AllData P)
        (.op (if b then .decr ptr ptr else .incr ptr ptr)) m 1 u := by
      cases b with
      | false => exact Eval.op_incr m ptr ptr hm hu
      | true => exact Eval.op_decr m ptr ptr hm hu
    obtain ⟨t,rest,hd,hp,hf⟩ := ih u hu
    refine ⟨t,?_,hd,?_,?_⟩
    · simpa [advance,List.replicate_succ,Block.straight,Nat.one_add] using one.seq rest
    · simpa [u,move_add,Nat.one_add] using hp
    · intro r hr
      simpa [u,hr] using hf r hr

private def body (back : Bool) (src dst value srcStride dstStride : Nat) : Block :=
  .seq (.op (.load value src)) <| .seq (.op (.store dst value)) <|
    .seq (advance back src srcStride) (advance back dst dstStride)

/-- Each copy uses one scratch scalar, two moving address registers, and a loop counter. -/
def block (back : Bool) (src dst counter length value srcStride dstStride : Nat) : Block :=
  .forRange counter length (body back src dst value srcStride dstStride)

private structure Inv {K : Type*} (P : K → Prop) (b : Bool) (src dst ctr value ss ds : Nat)
    (m : Memory K) (j : Nat) (t : Memory K) : Prop where
  safe : t.AllData P
  count : t.index ctr=j
  source : t.index src=address b (m.index src) ss j
  dest : t.index dst=address b (m.index dst) ds j
  indexFrame : ∀ r, r≠src → r≠dst → r≠ctr → t.index r=m.index r
  written : ∀ l<j, t.data (address b (m.index dst) ds l) = m.data (address b (m.index src) ss l)
  dataFrame : ∀ r, r≠value → (∀ l<j, r≠address b (m.index dst) ds l) → t.data r=m.data r

/-- Correct even when source and destination overlap: a write may touch its own read
or an earlier read. Distinct destination cells and preservation of every later read
are the only aliasing requirements. Zero source stride also permits broadcast. -/
theorem block_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (back : Bool) (src dst counter length value srcStride dstStride n : Nat)
    (hm : m.AllData P) (hn : m.index length=n) (hregs : [src,dst,counter,length].Nodup)
    (hstep : 0 < dstStride) (hroom : back=true → dstStride*(n-1) ≤ m.index dst)
    (hsrc : ∀ j<n, address back (m.index src) srcStride j ≠ value)
    (hdst : ∀ j<n, address back (m.index dst) dstStride j ≠ value)
    (hread : ∀ a j, a<j → j<n →
      address back (m.index dst) dstStride a ≠ address back (m.index src) srcStride j) :
    ∃ t, Eval (Memory.AllData P) (block back src dst counter length value srcStride dstStride)
        m (n*(srcStride+dstStride+5)+2) t ∧
      (∀ j<n, t.data (address back (m.index dst) dstStride j) =
        m.data (address back (m.index src) srcStride j)) ∧
      (∀ r, r≠value → (∀ j<n, r≠address back (m.index dst) dstStride j) → t.data r=m.data r) ∧
      t.index src=address back (m.index src) srcStride n ∧
      t.index dst=address back (m.index dst) dstStride n ∧ t.index counter=n ∧
      (∀ r, r≠src → r≠dst → r≠counter → t.index r=m.index r) := by
  have hsd : src≠dst := by rintro rfl; simp at hregs
  have hsc : src≠counter := by rintro rfl; simp at hregs
  have hsl : src≠length := by rintro rfl; simp at hregs
  have hdc : dst≠counter := by rintro rfl; simp at hregs
  have hdl : dst≠length := by rintro rfl; simp at hregs
  have hcl : counter≠length := by rintro rfl; simp at hregs
  let SA := address back (m.index src) srcStride
  let DA := address back (m.index dst) dstStride
  let I := Inv P back src dst counter value srcStride dstStride m
  have init : I 0 (m.putIndex counter 0) := by
    refine ⟨hm,by simp,by simp [hsc],by simp [hdc],?_,fun _ h => (Nat.not_lt_zero _ h).elim,
      fun _ _ _ => rfl⟩
    intro r _ _ hc
    simp [hc]
  obtain ⟨t,run,hfin⟩ := Eval.forRange_invariant_exact (safe := Memory.AllData P)
    (body := body back src dst value srcStride dstStride) counter length n
    (2+(srcStride+dstStride)) I m hm init
    (fun _ s h => ⟨h.safe,h.count,(h.indexFrame _ hsl.symm hdl.symm hcl.symm).trans hn⟩)
    (by
      intro j hj s hi
      have sourceVal : s.data (s.index src) = m.data (SA j) := by
        rw [hi.source]
        exact hi.dataFrame _ (hsrc j hj) (fun a ha => (hread a j ha hj).symm)
      let x := m.data (SA j)
      let loadState := s.putData value x
      let storeState := loadState.putData (DA j) x
      have px : P x := hm _
      have loadSafe : loadState.AllData P := hi.safe.putData value px
      have storeSafe : storeState.AllData P := loadSafe.putData _ px
      have loadRun : Eval (Memory.AllData P) (.op (.load value src)) s 1 loadState := by
        simpa only [loadState,x,sourceVal] using
          Eval.op_load s value src hi.safe (hi.safe.putData _ (hi.safe _))
      have destPtr : loadState.index dst = DA j := hi.dest
      have scratch : loadState.data value=x := Memory.putData_same s value x
      have storeRun : Eval (Memory.AllData P) (.op (.store dst value)) loadState 1 storeState := by
        simpa only [storeState,destPtr,scratch] using
          Eval.op_store loadState dst value loadSafe (by simpa only [destPtr,scratch] using storeSafe)
      obtain ⟨a,ea,da,pa,fa⟩ := advance_correct P storeState back src srcStride storeSafe
      obtain ⟨v,ev,dv,pv,fv⟩ := advance_correct P a back dst dstStride ea.safe_end
      refine ⟨v,?_,?_⟩
      · have h := loadRun.seq (storeRun.seq (ea.seq ev))
        rw [show 2+(srcStride+dstStride) = 1+(1+(srcStride+dstStride)) by omega]
        exact h
      · refine ⟨ev.safe_end,?_,?_,?_,?_,?_,?_⟩
        · simp [fv counter hdc.symm,fa counter hsc.symm,storeState,loadState,hi.count]
        · rw [Memory.putIndex_ne _ hsc, fv src hsd, pa]
          change move back (s.index src) srcStride = _
          rw [hi.source, advance_address]
        · rw [Memory.putIndex_ne _ hdc,pv, fa dst hsd.symm]
          change move back (s.index dst) dstStride = _
          rw [hi.dest,advance_address]
        · intro r rs rd rc
          rw [Memory.putIndex_ne _ rc, fv r rd, fa r rs]
          exact hi.indexFrame r rs rd rc
        · intro l hl
          change v.data (DA l) = m.data (SA l)
          rw [dv,da]
          by_cases e : l=j
          · subst l
            exact Memory.putData_same loadState _ x
          · have lt : l<j := by omega
            have ne : DA l≠DA j := address_ne hstep hroom lt hj
            rw [show storeState.data (DA l)=loadState.data (DA l) from Memory.putData_ne _ ne _]
            rw [show loadState.data (DA l)=s.data (DA l) from Memory.putData_ne _ (hdst l (lt.trans hj)) _]
            exact hi.written l lt
        · intro r rv hmiss
          change v.data r = m.data r
          rw [dv,da]
          have ne : r≠DA j := hmiss j (by omega)
          rw [show storeState.data r=loadState.data r from Memory.putData_ne _ ne _,
            show loadState.data r=s.data r from Memory.putData_ne _ rv _]
          exact hi.dataFrame r rv (fun l hl => hmiss l (by omega)))
  refine ⟨t,?_,hfin.written,hfin.dataFrame,hfin.source,hfin.dest,hfin.count,hfin.indexFrame⟩
  have e : n*(srcStride+dstStride+5)+2 = n*(2+(srcStride+dstStride)+3)+2 := by
    congr 2
    omega
  rw [e]
  exact run

@[simp] theorem address_forward (base stride j : Nat) : address false base stride j=base+stride*j := rfl

@[simp] theorem address_backward (base stride j : Nat) : address true base stride j=base-stride*j := rfl

/-- Disjoint enclosing windows are sufficient for the forward scan's read condition. -/
theorem forward_separated {srcBase dstBase srcStride dstStride n a j : Nat}
    (hs : 0 < srcStride) (hd : 0 < dstStride)
    (h : srcBase+srcStride*n ≤ dstBase ∨ dstBase+dstStride*n ≤ srcBase) (ha : a<n) (hj : j<n) :
    address false dstBase dstStride a ≠ address false srcBase srcStride j := by
  have u := Nat.mul_lt_mul_of_pos_left ha hd
  have v := Nat.mul_lt_mul_of_pos_left hj hs
  simp only [address_forward]
  omega

end StrideCopy
end RAM
end LinearProgramming
end Optimization
end OAI
