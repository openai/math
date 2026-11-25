import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import OAI.Optimization.LinearProgramming.Compression.SignWireOuterNormalize

/-! Stage an integer query row issued by the outer BitRAM into logical caller memory
of the nested numerical comparison. The numerical caller's cell j is the physical
scalar at 4j+2. The two outer header pointers contain actual physical addresses. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM

/-- Copy the raw pointers into mutable low even registers. Register 51 holds the count.
Only scalar zero is used outside the output row. -/
def outerRowScatter : Block :=
  .seq (.op (.addrCopy 4 53)) (.seq (.op (.addrCopy 6 55)) (StrideCopy.block false 4 6 8 51 0 1 4))

/-- The numerical comparator expects normalized low addresses after the scatter. -/
def outerRowStage : Block := .seq outerRowScatter outerNormalize

/-- The written row, complete scalar frame, and exact final physical address file. -/
structure OuterRowStaged {K : Type*} (m t : Memory K) (src base p : ℕ) : Prop where
  words : ∀ j<p, t.data (4*(base+j)+2) = m.data (src+j)
  scalars : ∀ r, r≠0 → (∀ j<p, r≠4*(base+j)+2) → t.data r=m.data r
  indices : ∀ r, t.index r = if r<64 ∧ r%2=0 then r%4 else m.index r

namespace OuterRowStaged

variable {K : Type*} {m t : Memory K} {src base p : ℕ}

theorem odd (s : OuterRowStaged m t src base p) (i : ℕ) (hi : i%2=1) :
    t.index i=m.index i := by
  rw [s.indices]
  split_ifs <;> omega

theorem high (s : OuterRowStaged m t src base p) (i : ℕ) (hi : 64≤ i) :
    t.index i=m.index i := by
  rw [s.indices]
  split_ifs <;> omega

theorem stableEven (s : OuterRowStaged m t src base p) : BitRAM.StableEven m t :=
  fun i hi _ => s.high i hi

theorem lowNative (s : OuterRowStaged m t src base p) (i : ℕ) (hi : i<16) : t.index (4*i)=0 := by
  rw [s.indices]
  split_ifs <;> omega

theorem lowCaller (s : OuterRowStaged m t src base p) (i : ℕ) (hi : i<16) : t.index (4*i+2)=2 := by
  rw [s.indices]
  split_ifs <;> omega

end OuterRowStaged

/-- Disjoint source and destination windows imply the weaker forward scan condition. -/
theorem outerRowScatter_separate {p src base : ℕ}
    (h : src+p ≤ 4*base+2 ∨ 4*(base+p)+2 ≤ src) (i j : ℕ) (hij : i<j) (hj : j<p) :
    4*(base+i)+2 ≠ src+j := by omega

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact count and overlapping-window precondition of the strided physical copy.
All address cells except the three even scratch registers are invariant. -/
theorem outerRowScatter_spec (P : K → Prop) (m : Memory K) (src base p : ℕ)
    (hm : m.AllData P) (hn : m.index 51=p) (hsrc : m.index 53=src) (hdst : m.index 55=4*base+2)
    (hnz : p=0 ∨ 0<src) (hread : ∀ i j, i<j → j<p → 4*(base+i)+2 ≠ src+j) :
    ∃ t, Block.Eval (Memory.AllData P) outerRowScatter m (10*p+4) t ∧
      (∀ j<p, t.data (4*(base+j)+2)=m.data (src+j)) ∧
      (∀ r, r≠0 → (∀ j<p, r≠4*(base+j)+2) → t.data r=m.data r) ∧
      (∀ r, r≠4 → r≠6 → r≠8 → t.index r=m.index r) := by
  let a := m.putIndex 4 (m.index 53)
  let b := a.putIndex 6 (a.index 55)
  have first := Block.Eval.op_addrCopy (safe := Memory.AllData P) m 4 53 hm hm
  have second := Block.Eval.op_addrCopy (safe := Memory.AllData P) a 6 55 hm hm
  have b4 : b.index 4=src := by simp [b,a,hsrc]
  have b6 : b.index 6=4*base+2 := by simp [b,a,hdst]
  have b51 : b.index 51=p := by simp [b,a,hn]
  have source (i : ℕ) : StrideCopy.address false (b.index 4) 1 i = src+i := by
    simp [StrideCopy.address,StrideCopy.move,b4]
  have dest (i : ℕ) : StrideCopy.address false (b.index 6) 4 i = 4*(base+i)+2 := by
    change b.index 6 + 4*i = 4*(base+i)+2
    rw [b6]
    omega
  obtain ⟨t,run,w,f,_,_,_,ix⟩ := StrideCopy.block_correct P b false 4 6 8 51 0 1 4 p hm b51
    (by decide) (by decide) (by simp)
    (by intro i hi; rw [source]; omega) (by intro i _; rw [dest]; omega)
    (by intro i j hij hj; rw [dest,source]; exact hread i j hij hj)
  have eval : Block.Eval (Memory.AllData P) outerRowScatter m (10*p+4) t := by
    simpa only [outerRowScatter,show 1+(1+(p*(1+4+5)+2))=10*p+4 by omega] using
      first.seq (second.seq run)
  refine ⟨t,eval,?_,?_,?_⟩
  · intro i hi
    calc
      t.data (4*(base+i)+2) = b.data (src+i) := by simpa only [source,dest] using w i hi
      _ = m.data (src+i) := rfl
  · intro r hr sep
    apply f r hr
    intro i hi
    rw [dest]
    exact sep i hi
  · intro r h4 h6 h8
    exact (ix r h4 h6 h8).trans ((Memory.putIndex_ne a h6 _).trans (Memory.putIndex_ne m h4 _))

/-- The complete stage both scatters the decoded source row and restores the nested
address convention. Its cost is exactly ten instructions per entry and 36 fixed
instructions. The outer VM registers and all high nested cache addresses survive. -/
theorem outerRowStage_spec (P : K → Prop) (m : Memory K) (src base p : ℕ)
    (hm : m.AllData P) (hn : m.index 51=p) (hsrc : m.index 53=src) (hdst : m.index 55=4*base+2)
    (hnz : p=0 ∨ 0<src) (hread : ∀ i j, i<j → j<p → 4*(base+i)+2 ≠ src+j) :
    ∃ t, Block.Eval (Memory.AllData P) outerRowStage m (10*p+36) t ∧ OuterRowStaged m t src base p := by
  obtain ⟨u,run,words,ds,ix⟩ := outerRowScatter_spec P m src base p hm hn hsrc hdst hnz hread
  have fin := outerNormalize_spec P u run.safe_end
  refine ⟨outerNormalized u,?_,?_,?_,?_⟩
  · exact run.seq fin
  · simpa only [outerNormalized_data] using words
  · simpa only [outerNormalized_data] using ds
  · intro r
    rw [outerNormalized_index]
    by_cases h : r<64 ∧ r%2=0
    · simp [h]
    · simp only [h,ite_false]
      apply ix r <;> rintro rfl <;> norm_num at h

/-- Specialize the stage to the integer row received by the word decoder. -/
theorem outerRowStage_words {p : ℕ} (P : K → Prop) (row : Fin p → ℤ) (m : Memory K)
    (src base : ℕ) (hm : m.AllData P) (hn : m.index 51=p) (hsrc : m.index 53=src)
    (hdst : m.index 55=4*base+2) (hnz : p=0 ∨ 0<src)
    (sep : src+p ≤ 4*base+2 ∨ 4*(base+p)+2 ≤ src)
    (data : ∀ i : Fin p, m.data (src+i.val)=(row i:K)) :
    ∃ t, (Callable.Fragment.ofBlock outerRowStage).Run P m (10*p+36) t ∧
      (∀ i : Fin p, t.data (4*(base+i.val)+2)=(row i:K)) ∧ OuterRowStaged m t src base p := by
  obtain ⟨t,run,frame⟩ := outerRowStage_spec P m src base p hm hn hsrc hdst hnz
    (outerRowScatter_separate sep)
  exact ⟨t,Callable.Fragment.Run.ofBlock run,fun i => (frame.words i i.isLt).trans (data i),frame⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
