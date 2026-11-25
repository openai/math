import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.ArrayFill
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMUpdate
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe

/-! RAM initialization of the rational label box and the terminal residual test. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM RAM.Block RAM.Dense
open scoped BigOperators Matrix

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Zero the coordinate array, seek its target coordinate, and give that coordinate
the lower endpoint one quarter. -/
def initBlock : Block :=
  .seq (.op (.const 0 0)) <| .seq (fillBlock 0 25 31 30 23) <|
    .seq (seekBlock 25 31 30 29) <|
    .seq (.op (.const 1 (1/4))) (.op (.store 31 1))

theorem initBlock_spec (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (p0 : P 0) (pquarter : P (1/4)) (hbase : 2 ≤ m.index 25)
    (htarget : m.index 29 < m.index 23) :
    ∃ t, Eval (Memory.AllData P) initBlock m (5*m.index 23+4*m.index 29+9) t ∧
      (∀ j < m.index 23, t.data (m.index 25+j) = if j = m.index 29 then 1/4 else 0) ∧
      (∀ r, 2 ≤ r → (r < m.index 25 ∨ m.index 25+m.index 23 ≤ r) → t.data r = m.data r) ∧
      (∀ r, r ≠ 30 → r ≠ 31 → t.index r = m.index r) := by
  let s0 := m.putData 0 0
  have h0 : s0.AllData P := hm.putData _ p0
  have e0 : Eval (Memory.AllData P) (.op (.const 0 0)) m 1 s0 := by
    simpa [s0] using Eval.op_const m 0 0 hm (by simpa using h0)
  obtain ⟨f,ef,cells,frame,_,_,fidx⟩ := fillBlock_correct P s0
    0 25 31 30 23 (m.index 23) (by decide) (by decide) (by decide) rfl (by change 0 < m.index 25; omega) h0
  have fbase : f.index 25 = m.index 25 := fidx _ (by decide) (by decide)
  have fi : f.index 29 = m.index 29 := fidx _ (by decide) (by decide)
  obtain ⟨q,eq,qd,_,qp,qidx⟩ := seekBlock_correct P f
    25 31 30 29 (m.index 29) (by decide) (by decide) (by decide) fi ef.safe_end
  rw [fbase] at qp
  let a := q.putData 1 (1/4)
  let t := a.putData (m.index 25+m.index 29) (1/4)
  have hq : q.AllData P := eq.safe_end
  have ha : a.AllData P := hq.putData _ pquarter
  have ht : t.AllData P := ha.putData _ pquarter
  have ec : Eval (Memory.AllData P) (.op (.const 1 (1/4))) q 1 a := by
    simpa [a] using Eval.op_const q 1 (1/4) hq (by simpa [a] using ha)
  have est : Eval (Memory.AllData P) (.op (.store 31 1)) a 1 t := by
    simpa only [a,Memory.putData_index,Memory.putData_same,qp,t] using
      Eval.op_store a 31 1 ha (by simpa [a,qp,t] using ht)
  refine ⟨t,?_,?_,?_,?_⟩
  · have run : Eval (Memory.AllData P) initBlock m
        (1+(5*m.index 23+3+(4*m.index 29+3+(1+1)))) t := e0.seq (ef.seq (eq.seq (ec.seq est)))
    rw [show 5*m.index 23+4*m.index 29+9 = 1+(5*m.index 23+3+(4*m.index 29+3+(1+1))) by omega]
    exact run
  · intro j hj
    by_cases he : j=m.index 29
    · subst j
      simp [t]
    · have hne' : m.index 25+j ≠ 1 := by omega
      have hc : f.data (m.index 25+j) = 0 := by simpa [s0] using cells j hj
      simp [he,t,a,hne',qd,hc]
  · intro r hr hout
    have hne : r ≠ m.index 25+m.index 29 := by omega
    have hf : f.data r = m.data r := by
      have hfor : r<s0.index 25 ∨ s0.index 25+m.index 23≤r := hout
      simpa [s0,show r ≠ 0 by omega] using frame r hfor
    simp [t,a,hne,show r ≠ 1 by omega,qd,hf]
  · intro r hi hp
    simpa [t,a,s0] using (qidx r hi hp).trans (fidx r hi hp)

/-- The actual square-sum of the first `k` entries in the residual buffer. -/
def energyPrefix (m : Memory K) (k : Nat) : K :=
  ∑ j ∈ Finset.range k, m.data (m.index 28+j)^2

def energyThreshold (n : Nat) : K := (1 / (1000*(n:K)))^2

/-- Register 28 addresses the residual array; scalar 11 carries the dimension. Register
19 receives one precisely when the computed squared residual is at most the threshold. -/
def energyBlock : Block :=
  .seq (.op (.addrCopy 20 28)) <| .seq (.op (.addrCopy 21 28)) <| .seq dotBlock <|
    .seq (.straight [.const 0 1000, .mul 1 0 11, .mul 2 1 1, .const 3 1, .div 4 3 2])
      (.branch (.scalarLT 4 20) (.op (.const 19 0)) (.op (.const 19 1)))

theorem energyBlock_spec (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (hn : 0 < m.index 23) (hbase : 23 < m.index 28) (hscalar : m.data 11 = (m.index 23 : K))
    (p0 : P 0) (p1 : P 1) (p1000 : P 1000)
    (p1000n : P (1000*(m.index 23:K))) (psq : P ((1000*(m.index 23:K))^2))
    (pτ : P (energyThreshold (K:=K) (m.index 23)))
    (hterm : ∀ j < m.index 23, P (m.data (m.index 28+j)^2))
    (hprefix : ∀ j ≤ m.index 23, P (energyPrefix m j)) :
    ∃ t k, k ≤ 9*m.index 23+13 ∧ Eval (Memory.AllData P) energyBlock m k t ∧
      t.data 19 = (if energyPrefix m (m.index 23) ≤ energyThreshold (m.index 23) then 1 else 0) ∧
      (∀ r, 5 ≤ r → (r < 19 ∨ 23 < r) → t.data r = m.data r) ∧
      (∀ r, r < 20 ∨ 22 < r → t.index r = m.index r) := by
  let l := m.putIndex 20 (m.index 28)
  let r := l.putIndex 21 (m.index 28)
  have el : Eval (Memory.AllData P) (.op (.addrCopy 20 28)) m 1 l :=
    Eval.op_addrCopy m 20 28 hm hm
  have er : Eval (Memory.AllData P) (.op (.addrCopy 21 28)) l 1 r := by
    simpa [r,l] using Eval.op_addrCopy l 21 28 hm hm
  have dot (j : Nat) : dotTerm r j = m.data (m.index 28+j)^2 := by
    simp [dotTerm,r,l,pow_two]
  have pref (j : Nat) : dotPrefix r j = energyPrefix m j := by simp [dotPrefix,energyPrefix,dot]
  obtain ⟨s,run,post⟩ := dotBlock_correct P r (m.index 23) hm
    (by simpa [r,l] using hbase) (by simpa [r,l] using hbase) (by simp [r,l])
    (fun j hj => (dot j).symm ▸ hterm j hj) (fun j hj => (pref j).symm ▸ hprefix j hj)
  have hs : s.AllData P := run.safe_end
  have hsum : s.data 20 = energyPrefix m (m.index 23) := post.sum.trans (pref _)
  have hs11 : s.data 11 = (m.index 23 : K) := (post.dataFrame _ (Or.inl (by decide))).trans hscalar
  let w := (1000 : K)*(m.index 23:K)
  let v := energyThreshold (K:=K) (m.index 23)
  have hw : w ≠ 0 := by dsimp [w]; positivity
  have hv : (1 : K)/(w^2) = v := by
    change 1 / w^2 = (1 / w)^2
    rw [div_pow,one_pow]
  let s0 := s.putData 0 1000
  let s1 := s0.putData 1 w
  let s2 := s1.putData 2 (w^2)
  let s3 := s2.putData 3 1
  let s4 := s3.putData 4 v
  have h0 : s0.AllData P := hs.putData _ p1000
  have h1 : s1.AllData P := h0.putData _ p1000n
  have h2 : s2.AllData P := h1.putData _ psq
  have h3 : s3.AllData P := h2.putData _ p1
  have h4 : s4.AllData P := h3.putData _ pτ
  have e0 : Eval (Memory.AllData P) (.op (.const 0 1000)) s 1 s0 := by
    simpa [s0] using Eval.op_const s 0 1000 hs (by simpa using h0)
  have hprod : s0.data 0*s0.data 11=w := by simp [s0,w,hs11]
  have e1 : Eval (Memory.AllData P) (.op (.mul 1 0 11)) s0 1 s1 := by
    simpa only [s1,hprod] using Eval.op_mul s0 1 0 11 h0 (by rw [hprod]; exact h1)
  have hpow : s1.data 1*s1.data 1=w^2 := by simp [s1,pow_two]
  have e2 : Eval (Memory.AllData P) (.op (.mul 2 1 1)) s1 1 s2 := by
    simpa only [s2,hpow] using Eval.op_mul s1 2 1 1 h1 (by rw [hpow]; exact h2)
  have e3 : Eval (Memory.AllData P) (.op (.const 3 1)) s2 1 s3 := by
    simpa [s3] using Eval.op_const s2 3 1 h2 (by simpa using h3)
  have denom : s3.data 2 ≠ 0 := by simpa [s3,s2] using pow_ne_zero 2 hw
  have hdiv : s3.data 3/s3.data 2 = v := by simpa [s3,s2] using hv
  have e4 : Eval (Memory.AllData P) (.op (.div 4 3 2)) s3 1 s4 := by
    simpa only [s4,hdiv] using Eval.op_div s3 4 3 2 denom h3 (by rw [hdiv]; exact h4)
  have calcRun : Eval (Memory.AllData P)
      (.straight [.const 0 1000,.mul 1 0 11,.mul 2 1 1,.const 3 1,.div 4 3 2]) s 5 s4 :=
    e0.seq (e1.seq (e2.seq (e3.seq (e4.seq (.skip h4)))))
  let result : K := if energyPrefix m (m.index 23) ≤ v then 1 else 0
  let t := s4.putData 19 result
  have branchRun : ∃ k ≤ 3, Eval (Memory.AllData P)
      (.branch (.scalarLT 4 20) (.op (.const 19 0)) (.op (.const 19 1))) s4 k t := by
    by_cases h : energyPrefix m (m.index 23) ≤ v
    · have guard : (Cond.scalarLT 4 20).test s4 = false := by
        simp [Cond.test,s4,s3,s2,s1,s0,hsum,not_lt_of_ge h]
      refine ⟨2,by decide,Eval.branchFalse (k:=1) guard ?_⟩
      simpa [t,result,h] using Eval.op_const s4 19 1 h4 (by simpa using h4.putData 19 p1)
    · have guard : (Cond.scalarLT 4 20).test s4 = true := by
        simp [Cond.test,s4,s3,s2,s1,s0,hsum,lt_of_not_ge h]
      refine ⟨3,by decide,Eval.branchTrue (k:=1) guard ?_⟩
      simpa [t,result,h] using Eval.op_const s4 19 0 h4 (by simpa using h4.putData 19 p0)
  obtain ⟨k,hk,eb⟩ := branchRun
  refine ⟨t,1+(1+(9*m.index 23+3+(5+k))),by omega,el.seq (er.seq (run.seq (calcRun.seq eb))),?_,?_,?_⟩
  · simp [t,result,v]
  · intro j hj hf
    have hd := post.dataFrame j (by omega)
    simpa [t,s4,s3,s2,s1,s0,r,l,show j ≠ 0 by omega,show j ≠ 1 by omega,
      show j ≠ 2 by omega,show j ≠ 3 by omega,show j ≠ 4 by omega, show j ≠ 19 by omega] using hd
  · intro j hj
    simpa [t,s4,s3,s2,s1,s0,r,l,show j ≠ 20 by omega,show j ≠ 21 by omega] using post.indexFrame j hj

omit [IsStrictOrderedRing K] in
/-- The RAM's two comparisons select precisely the corner used by the mathematical update. -/
theorem cellValue_eq_fwStep {n : Nat} (Q : Matrix (Fin n) (Fin n) K) (hs : Qᵀ = Q)
    (he : Q*Q=Q) (i j : Fin n) (z : Fin n → K) (a : K) :
    cellValue i j a ((Q *ᵥ z) j) (z j) = fwStep Q i z a j := by
  have hh : (Q *ᵥ z) ᵥ* Q = Q *ᵥ z := by
    rw [← Matrix.mulVec_transpose,hs,Matrix.mulVec_mulVec,he]
  have hc : cellCorner (i:Nat) (j:Nat) ((Q *ᵥ z) j) = fwCorner i (Q *ᵥ z) j := by
    by_cases g : (Q *ᵥ z) j < 0
    · simp [cellCorner,fwCorner,g,not_le_of_gt g]
    · by_cases eq : j=i
      · subst j
        simp [cellCorner,fwCorner,fwLower,g,le_of_not_gt g]
      · have neq : j.val ≠ i.val := by simpa [Fin.ext_iff] using eq
        simp [cellCorner,fwCorner,fwLower,g,le_of_not_gt g,eq,neq]
  simp [cellValue,fwStep,hh,hc]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem energyPrefix_eq_fwEnergy {n : Nat} (m : Memory K) (Q : Matrix (Fin n) (Fin n) K)
    (z : Fin n → K) (hg : ∀ j : Fin n, m.data (m.index 28+j.val) = (Q *ᵥ z) j) :
    energyPrefix m n = fwEnergy Q z := by
  unfold energyPrefix fwEnergy dotProduct
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [hg j, pow_two]

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
