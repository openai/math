import OAI.Optimization.LinearProgramming.Compression.ServiceStageSlotBlock
import OAI.Optimization.LinearProgramming.Compression.ServiceCanonicalWords

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

/-- Scalar words written by the staging ROM, independent of the interpretation
of the scalar in register 5. The two scratch scalars are 0 and 6. -/
structure RawSlotStaged {K : Type*} [Field K] {d e n : ℕ} (u : PairMinorIndex d e n)
    (dst : ℕ) (s t : Memory K) : Prop where
  tag : t.data dst = (GeneratorTable.tag u : K)
  order : t.data (dst+1) = (GeneratorTable.order u : K)
  rows : ∀ i : Fin n, t.data (dst+2+i.val) = (rowWord u i.val : K)
  cols : ∀ i : Fin n, t.data (dst+2+n+i.val) = (colWord u i.val : K)
  magnitude : t.data (dst+2+2*n)=s.data 5
  data : ∀ a, a ≠ 0 → a ≠ 6 → (a < dst ∨ dst+stride n ≤ a) → t.data a=s.data a
  indices : ∀ a, a ≠ 26 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 30 → t.index a=s.index a

set_option maxHeartbeats 1400000 in
/-- Stage the tag, order and both padded coordinate arrays of any minor index,
then copy its accompanying field value. Every address read and scalar operation
is an instruction of the same fixed program. -/
theorem stageSlot_raw {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d e n : ℕ} (u : PairMinorIndex d e n) (P : K → Prop) (s : Memory K) (dst : ℕ) (hdim : d+e=n)
    (h21 : s.index 21=dst) (h22 : s.index 22=n) (hlow : 7 ≤ dst) (hwire : Wire u s)
    (hs : ∀ a, P (s.data a)) (hv : ∀ j ≤ max n 1, P (j:K)) :
    ∃ t l, l ≤ 40*(n+1)^2 ∧ Block.Eval (fun z => ∀ a, P (z.data a)) stageSlot s l t ∧
      RawSlotStaged u dst s t := by
  let safe := fun z : Memory K => ∀a,P (z.data a)
  let a := applyPlan stagePointers s
  have ea : Block.Eval safe (addressPlan stagePointers) s 3 a := addressPlan_spec (fun f => ∀j,P (f j)) _ _ hs
  have a26 : a.index 26 = dst := by simp [a,stagePointers,applyPlan,AddressSet.apply,h21]
  have a27 : a.index 27 = s.index 40+2 := by simp [a,stagePointers,applyPlan,AddressSet.apply,Nat.add_assoc]
  have ai (j : ℕ) (h₁ : j ≠ 26) (h₂ : j ≠ 27) : a.index j = s.index j := by simp [a,stagePointers,applyPlan,AddressSet.apply,h₁,h₂]
  have hone : P 1 := by simpa using hv 1 (le_max_right _ _)
  have hk := order_le u
  have htag := tag_le u
  obtain ⟨b,eb,bval,b26,bd,bi⟩ := GeneratorTable.smallStore_spec P a 43 (tag u) dst (by decide)
    ((ai 43 (by decide) (by decide)).trans hwire.side) a26 ea.safe_end hone (fun j hj => hv j (hj.trans (htag.trans (le_max_right _ _))))
  obtain ⟨c,ec,cval,c26,cd,ci⟩ := GeneratorTable.smallStore_spec P b 42 (order u) (dst+1) (by decide)
    ((bi 42 (by decide) (by decide)).trans ((ai 42 (by decide) (by decide)).trans hwire.size)) b26 eb.safe_end hone
    (fun j hj => hv j (hj.trans (hk.trans (le_max_left _ _))))
  have cidx (j : ℕ) (h26' : j ≠ 26) (h27' : j ≠ 27) (h30 : j ≠ 30) : c.index j = s.index j :=
    (ci j h26' h30).trans ((bi j h26' h30).trans (ai j h26' h27'))
  have c22 := (cidx 22 (by decide) (by decide) (by decide)).trans h22
  have c42 := (cidx 42 (by decide) (by decide) (by decide)).trans hwire.size
  have c27 := (ci 27 (by decide) (by decide)).trans ((bi 27 (by decide) (by decide)).trans a27)
  have hb := hwire.base
  have hnat (j : ℕ) (hj : j ≤ n) := hv j (hj.trans (le_max_left _ _))
  obtain ⟨r,k,kr,er,rr⟩ := stageArray_spec P c n (order u) (s.index 40+2) (dst+2) (rowWord u)
    hk (by omega) (by omega) c22 c42 c26 c27
    (fun i hi => (cidx _ (by omega) (by omega) (by omega)).trans (hwire.rows i hi)) (row_padding u)
    (fun i _ => rowWord_le u hdim i) ec.safe_end hone hnat
  have r22 := (rr.indices 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans c22
  have r42 := (rr.indices 42 (by decide) (by decide) (by decide) (by decide) (by decide)).trans c42
  obtain ⟨v,l,kl,ev,rv⟩ := stageArray_spec P r n (order u) (s.index 40+2+order u) (dst+2+n) (colWord u)
    hk (by omega) (by omega) r22 r42 rr.outPtr rr.inPtr
    (fun i hi => (rr.indices _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      ((cidx _ (by omega) (by omega) (by omega)).trans (hwire.cols i hi))) (col_padding u)
    (fun i _ => colWord_le u i) er.safe_end hone hnat
  have vi26 : v.index 26 = dst+2+2*n := by rw [rv.outPtr]; omega
  have v5 : v.data 5=s.data 5 := by
    rw [rv.data 5 (by decide) (by decide) (by omega),rr.data 5 (by decide) (by decide) (by omega),
      cd 5 (by decide) (by decide) (by omega),bd 5 (by decide) (by decide) (by omega),
      show a.data = s.data from applyPlan_data _ _]
  let t := v.putData (v.index 26) (v.data 5)
  have st : safe t := by
    intro j
    by_cases h : j = v.index 26
    · simpa [t,h] using ev.safe_end 5
    · simpa [t,h] using ev.safe_end j
  have et : Block.Eval safe (.op (.store 26 5)) v 1 t := Block.Eval.op_store _ _ _ ev.safe_end st
  refine ⟨t,3+((4*tag u+6)+((4*order u+6)+(k+(l+1)))),?_,ea.seq (eb.seq (ec.seq (er.seq (ev.seq et)))),?_⟩
  · have ub : n*(4*n+13)+2 = 4*n^2+13*n+2 := by ring
    rw [ub] at kr kl
    ring_nf; omega
  · refine ⟨?_,?_,?_,?_,by simp [t,vi26,v5],?_,?_⟩
    · have ic : c.data dst = (tag u:K) := (cd dst (by omega) (by omega) (by omega)).trans bval
      simpa [t,vi26,show dst ≠ dst+2+2*n by omega] using (rv.data dst (by omega) (by omega) (by omega)).trans
        ((rr.data dst (by omega) (by omega) (by omega)).trans ic)
    · simpa [t,vi26,show dst+1 ≠ dst+2+2*n by omega] using (rv.data (dst+1) (by omega) (by omega) (by omega)).trans
        ((rr.data (dst+1) (by omega) (by omega) (by omega)).trans cval)
    · intro i
      have hi := i.isLt
      have keep : dst+2+i.val ≠ v.index 26 := by rw [vi26];omega
      exact (Memory.putData_ne v keep (v.data 5)).trans
        ((rv.data (dst+2+i.val) (by omega) (by omega) (by omega)).trans (rr.writes _ hi))
    · intro i
      have hi := i.isLt
      have keep : dst+2+n+i.val ≠ v.index 26 := by rw [vi26];omega
      exact (Memory.putData_ne v keep (v.data 5)).trans (rv.writes _ hi)
    · intro j h0 h6 hout
      unfold stride at hout
      have eq := (rv.data j h0 h6 (by omega)).trans ((rr.data j h0 h6 (by omega)).trans
        ((cd j h0 h6 (by omega)).trans ((bd j h0 h6 (by omega)).trans (congrFun (applyPlan_data _ _) j))))
      simpa [t,vi26,show j ≠ dst+2+2*n by omega] using eq
    · intro j h26 h27 h28 h29 h30
      exact (rv.indices j h26 h27 h28 h29 h30).trans ((rr.indices j h26 h27 h28 h29 h30).trans (cidx j h26 h27 h30))

structure SlotStaged {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (q : NonzeroPairMinor D E) (dst : ℕ) (s t : Memory ℚ) : Prop where
  slot : SlotAt D E q dst t
  data : ∀ a,a ≠ 0 → a ≠ 6 → (a < dst ∨ dst+stride n ≤ a) → t.data a = s.data a
  indices : ∀ a,a ≠ 26 → a ≠ 27 → a ≠ 28 → a ≠ 29 → a ≠ 30 → t.index a = s.index a

/-- The staging procedure reads actual canonical words, rounds no coordinate, and preserves
the original matrices and every previously stored generator. -/
theorem stageSlot_spec {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (q : NonzeroPairMinor D E) (P : ℚ→Prop) (s : Memory ℚ) (dst : ℕ) (hdim : d+e = n)
    (h21 : s.index 21 = dst) (h22 : s.index 22 = n) (hlow : 7 ≤ dst) (hwire : Wire q.val s)
    (hmag : s.data 5=|pairMinorValue D E q.val|) (hs : ∀a,P (s.data a))
    (hv : ∀ j ≤ max n 1,P (j:ℚ)) :
    ∃ t l,l ≤ 40*(n+1)^2 ∧ Block.Eval (fun z => ∀a,P (z.data a)) stageSlot s l t ∧ SlotStaged D E q dst s t := by
  obtain ⟨t,l,hl,run,raw⟩ := GeneratorTable.stageSlot_raw q.val P s dst hdim h21 h22 hlow hwire hs hv
  exact ⟨t,l,hl,run,⟨⟨raw.tag,raw.order,raw.rows,raw.cols,raw.magnitude.trans hmag⟩,
    raw.data,raw.indices⟩⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
