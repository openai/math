import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import Mathlib.Tactic

/-! Copy compacted bases into the caller's ordinary scalar staging array, including
the four reserved registers of the native signed-product machine. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def writeScalarHeader : List ℚ → Block
  | [] => .skip
  | c::cs => .seq (.op (.const 0 c)) (.seq (.op (.store 6 0))
      (.seq (.op (.incr 6 6)) (writeScalarHeader cs)))

private theorem writeScalarHeader_spec (cs : List ℚ) (m : Memory K) (dst : ℕ) {P : K → Prop}
    (hm : m.AllData P) (hc : ∀ c ∈ cs, P (c : K)) (hdst : m.index 6 = dst) (hp : 0 < dst) :
    ∃ t, Block.Eval (Memory.AllData P) (writeScalarHeader cs) m (3*cs.length) t ∧
      t.index 6 = dst+cs.length ∧
      (∀ i, ∀ hi : i < cs.length, t.data (dst+i) = (cs[i] : K)) ∧
      (∀ j, j ≠ 0 → (j < dst ∨ dst+cs.length ≤ j) → t.data j = m.data j) ∧
      ∀ j, j ≠ 6 → t.index j = m.index j := by
  induction cs generalizing m dst with
  | nil => exact ⟨m,.skip hm,by simpa using hdst,by simp,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | cons c cs ih =>
    let a := m.putData 0 (c : K)
    let b := a.putData dst (c : K)
    let v := b.putIndex 6 (dst+1)
    have hpc := hc c (by simp)
    have ha : a.AllData P := hm.putData 0 hpc
    have hb : b.AllData P := ha.putData dst hpc
    have ea : Block.Eval (Memory.AllData P) (.op (.const 0 c)) m 1 a := Block.Eval.op_const _ _ _ hm ha
    have eb : Block.Eval (Memory.AllData P) (.op (.store 6 0)) a 1 b := by
      simpa [a,b,hdst] using Block.Eval.op_store (safe := Memory.AllData P) a 6 0 ha
        (ha.putData (a.index 6) (ha 0))
    have ev : Block.Eval (Memory.AllData P) (.op (.incr 6 6)) b 1 v := by
      simpa [v,b,a,hdst] using Block.Eval.op_incr (safe := Memory.AllData P) b 6 6 hb hb
    obtain ⟨t,et,ht,words,df,ii⟩ := ih v (dst+1) ev.safe_end (fun x hx => hc x (by simp [hx]))
      (by simp [v]) (by omega)
    refine ⟨t,?_,?_,?_,?_,?_⟩
    · convert ea.seq (eb.seq (ev.seq et)) using 1 <;> first | rfl | omega | (simp only [List.length_cons]; omega)
    · simp only [List.length_cons]; omega
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero,df dst (by omega) (Or.inl (by omega))]
        simp [v,b]
      | succ j =>
        have hh := words j (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · intro i hi hfree
      rw [df i hi (by simp only [List.length_cons] at hfree; omega)]
      have hn : i ≠ dst := by simp only [List.length_cons] at hfree; omega
      simp [v,b,a,hi,hn]
    · intro i hi
      simpa [v,b,a,hi] using ii i hi

private def initBasePointers : Block :=
  Block.straight [.addrCopy 6 55, .addrCopy 7 51, .addrCopy 56 50,
    .incr 56 56, .incr 56 56, .incr 56 56, .incr 56 56]

private theorem initBasePointers_spec (m : Memory K) {P : K → Prop} (hm : m.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) initBasePointers m 7 t ∧ t.data = m.data ∧
      t.index 6 = m.index 55 ∧ t.index 7 = m.index 51 ∧ t.index 56 = m.index 50+4 ∧
      ∀ j, j ≠ 6 → j ≠ 7 → j ≠ 56 → t.index j = m.index j := by
  let a := m.putIndex 6 (m.index 55)
  let b := a.putIndex 7 (a.index 51)
  let c := b.putIndex 56 (b.index 50)
  let d := c.putIndex 56 (c.index 56+1)
  let e := d.putIndex 56 (d.index 56+1)
  let f := e.putIndex 56 (e.index 56+1)
  let g := f.putIndex 56 (f.index 56+1)
  refine ⟨g,?_,rfl,?_,?_,?_,?_⟩
  · exact .seq (Block.Eval.op_addrCopy m 6 55 hm hm) <| .seq (Block.Eval.op_addrCopy a 7 51 hm hm) <|
      .seq (Block.Eval.op_addrCopy b 56 50 hm hm) <| .seq (Block.Eval.op_incr c 56 56 hm hm) <|
      .seq (Block.Eval.op_incr d 56 56 hm hm) <| .seq (Block.Eval.op_incr e 56 56 hm hm) <|
      .seq (Block.Eval.op_incr f 56 56 hm hm) (.skip hm)
  all_goals first | (intro j h6 h7 h56; simp [g,f,e,d,c,b,a,h6,h7,h56]) | simp [g,f,e,d,c,b,a]

/-- Register 51 points at the compacted bases, 50 is their count, and 55 points at
the staged output. Register 56 is filled with its total length. -/
def packPowerBasesBlock : Block :=
  .seq initBasePointers (.seq (writeScalarHeader [0,1,1,1])
    (StrideCopy.block false 7 6 8 50 0 1 1))

def powerPairScalarWords (xs : List K) : List K := [0,1,1,1] ++ xs

theorem packPowerBasesBlock_spec (xs : List K) (m : Memory K) (src dst : ℕ) {P : K → Prop}
    (hm : m.AllData P) (h0 : P 0) (h1 : P 1) (hn : m.index 50 = xs.length)
    (hs : m.index 51 = src) (hd : m.index 55 = dst) (hsrc : 64 ≤ src) (hdst : 64 ≤ dst)
    (hsep : src+xs.length ≤ dst ∨ dst+4+xs.length ≤ src)
    (values : ∀ i, ∀ hi : i < xs.length, m.data (src+i) = xs[i]) :
    ∃ t, Block.Eval (Memory.AllData P) packPowerBasesBlock m (7*xs.length+21) t ∧
      t.index 56 = (powerPairScalarWords xs).length ∧
      (∀ i, ∀ hi : i < (powerPairScalarWords xs).length, t.data (dst+i) = (powerPairScalarWords xs)[i]) ∧
      (∀ i, i ≠ 0 → (i < dst ∨ dst+(powerPairScalarWords xs).length ≤ i) → t.data i = m.data i) ∧
      ∀ i, i ≠ 6 → i ≠ 7 → i ≠ 8 → i ≠ 56 → t.index i = m.index i := by
  obtain ⟨a,ea,ad,a6,a7,a56,ai⟩ := initBasePointers_spec m hm
  have hc : ∀ c ∈ ([0,1,1,1] : List ℚ), P (c : K) := by
    intro c h; simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at h
    rcases h with rfl | rfl <;> simpa using (by first | exact h0 | exact h1)
  obtain ⟨b,eb,b6,hhead,bd,bi⟩ := writeScalarHeader_spec [0,1,1,1] a dst ea.safe_end hc
    (a6.trans hd) (by omega)
  have b7 : b.index 7 = src := (bi 7 (by decide)).trans (a7.trans hs)
  have bdst : b.index 6 = dst+4 := b6
  have bn : b.index 50 = xs.length :=
    (bi 50 (by decide)).trans ((ai 50 (by decide) (by decide) (by decide)).trans hn)
  obtain ⟨t,et,hcopy,tf,_,_,_,ti⟩ :=
    StrideCopy.block_correct P b false 7 6 8 50 0 1 1 xs.length eb.safe_end bn (by decide)
      (by decide) (by simp) (fun j hj => by simp [StrideCopy.address,StrideCopy.move,b7]; omega)
      (fun j _ => by simp [StrideCopy.address,StrideCopy.move,bdst])
      (fun i j hij hj => by simp [StrideCopy.address,StrideCopy.move,b7,bdst]; omega)
  refine ⟨t,?_,?_,?_,?_,?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · rw [ti 56 (by decide) (by decide) (by decide),bi 56 (by decide),a56,hn]
    simp only [powerPairScalarWords,List.length_append,List.length_cons,List.length_nil];omega
  · intro j hj
    by_cases hlow : j < 4
    · have hz : t.data (dst+j) = b.data (dst+j) := tf _ (by omega)
        (fun i _ => by simp [StrideCopy.address,StrideCopy.move,bdst];omega)
      rw [hz]
      have hh := hhead j (by simpa using hlow)
      interval_cases j <;> simpa [powerPairScalarWords] using hh
    · have hj' : j-4 < xs.length := by
        simp [powerPairScalarWords] at hj; omega
      have hc' := hcopy (j-4) hj'
      simp only [StrideCopy.address,StrideCopy.move, Bool.false_eq_true, ite_false,
        b7, bdst, Nat.one_mul] at hc'
      have he : dst+4+(j-4)=dst+j := by omega
      rw [he] at hc'
      rw [hc',bd _ (by omega) (by simp; omega),ad,values (j-4) hj']
      exact (List.getElem_append_right (show ([0,1,1,1] : List K).length ≤ j by simpa using Nat.le_of_not_gt hlow)).symm
  · intro i hne hf
    have hf' : i < dst ∨ dst+4+xs.length ≤ i := by
      simp only [powerPairScalarWords,List.length_append,List.length_cons,List.length_nil] at hf; omega
    rw [tf i hne (fun j hj => by simp [StrideCopy.address,StrideCopy.move,bdst];omega),
      bd i hne (by simp; omega),ad]
  · intro i h6 h7 h8 h56
    exact (ti i h7 h6 h8).trans ((bi i h6).trans (ai i h6 h7 h56))

end Compression
end LinearProgramming
end Optimization
end OAI
