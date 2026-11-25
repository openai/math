import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! A native gather with a runtime row stride and a contiguous scalar destination. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def gatherBody : Block := .seq (.op (.load 6 8)) (.seq (.op (.store 9 6))
  (.seq (cellAddress 8 10 11 8 18 2 18) (.seq (.op (.incr 9 9)) (.op (.incr 15 15)))))

def gatherLoop : Block := .loop (.addrLT 15 17) gatherBody

private structure Gathered (P : K→Prop) (src dst width : ℕ) (start : Memory K) (i : ℕ) (s : Memory K) : Prop where
  safe : ∀ j,P (s.data j)
  source : s.index 8 = src+i*width
  dest : s.index 9 = dst+i
  counter : s.index 15 = i
  copied : ∀ j < i,s.data (dst+j) = start.data (src+j*width)
  data : ∀ j,j ≠ 6 → (j < dst ∨ dst+i ≤ j) → s.data j = start.data j
  index : ∀ j,j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 15 → s.index j = start.index j

/-- The gather reads each source once and charges an increment for every unit of stride. -/
theorem gatherLoop_spec (P : K→Prop) (s : Memory K) (g src dst width : ℕ)
    (hr : 7 ≤ src) (hd : 7 ≤ dst) (sep : ∀ i < g,src+i*width < dst)
    (h2 : s.index 2 = 0) (h8 : s.index 8 = src) (h9 : s.index 9 = dst) (h15 : s.index 15 = 0)
    (h17 : s.index 17 = g) (h18 : s.index 18 = width) (hs : ∀ j,P (s.data j)) :
    ∃t,Block.Eval (fun z => ∀ j,P (z.data j)) gatherLoop s (g*(4*width+11)+1) t ∧
      t.index 9 = dst+g ∧ (∀ i < g,t.data (dst+i) = s.data (src+i*width)) ∧
      (∀ j,j ≠ 6 → (j < dst ∨ dst+g ≤ j) → t.data j = s.data j) ∧
      ∀ j,j ≠ 8 → j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 15 → t.index j = s.index j := by
  let safe := fun z : Memory K => ∀ j,P (z.data j)
  let I := Gathered P src dst width s
  have init : I 0 s := ⟨hs,by simpa using h8,by simpa using h9,h15,fun _ h => (Nat.not_lt_zero _ h).elim,
    fun _ _ _ => rfl,fun _ _ _ _ _ _ => rfl⟩
  have step (i : ℕ) (hi : i < g) (m : Memory K) (hm : I i m) : (Cond.addrLT 15 17).test m = true ∧
      ∃t,Block.Eval safe gatherBody m (4*width+9) t ∧ I (i+1) t := by
    have m17 := (hm.index 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17
    refine ⟨by simpa [Cond.test,hm.counter,m17] using hi,?_⟩
    let a := m.putData 6 (m.data (m.index 8))
    let b := a.putData (a.index 9) (a.data 6)
    have good {m : Memory K} {r : ℕ} {v : K} (hs' : safe m) (hv : P v) : safe (m.putData r v) := by
      intro j;by_cases hj : j = r
      · simpa [hj] using hv
      · simpa [hj] using hs' j
    have sa : safe a := good hm.safe (hm.safe _)
    have sb : safe b := good sa (sa 6)
    have ea : Block.Eval safe (.op (.load 6 8)) m 1 a := Block.Eval.op_load _ _ _ hm.safe sa
    have eb : Block.Eval safe (.op (.store 9 6)) a 1 b := Block.Eval.op_store _ _ _ sa sb
    obtain ⟨c,ec,cd,ci,c8⟩ := cellAddress_spec (fun f => ∀ j,P (f j)) b sb 8 10 11 8 18 2 18 (by simp [CellScratchOK])
    have b2 : b.index 2 = 0 := (hm.index 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
    have b18 : b.index 18 = width := (hm.index 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h18
    rw [b2,b18] at ec c8
    simp only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] at ec c8
    let d := c.putIndex 9 (c.index 9+1)
    let t := d.putIndex 15 (d.index 15+1)
    have ed : Block.Eval safe (.op (.incr 9 9)) c 1 d := Block.Eval.op_incr _ _ _ ec.safe_end ec.safe_end
    have et : Block.Eval safe (.op (.incr 15 15)) d 1 t := Block.Eval.op_incr _ _ _ ed.safe_end ed.safe_end
    have got : a.data 6 = s.data (src+i*width) := by
      simp only [a,Memory.putData_same,hm.source]
      exact hm.data _ (by omega) (Or.inl (sep i hi))
    refine ⟨t,?_,et.safe_end,?_,?_,?_,?_,?_,?_⟩
    · have addrRun : Block.Eval safe (cellAddress 8 10 11 8 18 2 18) b (4*width+5) c := ec
      have bodyCost : 1+(1+((4*width+5)+(1+1))) = 4*width+9 := by omega
      rw [← bodyCost]
      exact ea.seq (eb.seq (addrRun.seq (ed.seq et)))
    · simp [t,d,c8,b,a,hm.source,Nat.add_mul,Nat.add_assoc]
    · simp [t,d,ci 9 (by decide) (by decide) (by decide),b,a,hm.dest,Nat.add_assoc]
    · simp [t,d,ci 15 (by decide) (by decide) (by decide),b,a,hm.counter]
    · intro j hj
      change c.data (dst+j) = _
      rw [cd]
      by_cases he : j = i
      · subst j
        change (a.putData (a.index 9) (a.data 6)).data (dst+i) = _
        rw [show a.index 9 = dst+i from hm.dest,Memory.putData_same,got]
      · have jlo : j < i := by omega
        change (a.putData (a.index 9) (a.data 6)).data (dst+j) = _
        rw [Memory.putData_ne _ (by change dst+j ≠ m.index 9;rw [hm.dest];omega)]
        exact (Memory.putData_ne m (by omega : dst+j ≠ 6) _).trans (hm.copied j jlo)
    · intro j h6 hout
      change c.data j = _
      rw [cd]
      change (a.putData (a.index 9) (a.data 6)).data j = _
      rw [Memory.putData_ne _ (by change j ≠ m.index 9;rw [hm.dest];omega)]
      exact (Memory.putData_ne m h6 _).trans (hm.data j h6 (by omega))
    · intro j h8' h9' h10 h11 h15'
      simpa [t,d,h9',h15',b,a] using (ci j h8' h10 h11).trans (hm.index j h8' h9' h10 h11 h15')
  have stop (t : Memory K) (ht : I g t) : (Cond.addrLT 15 17).test t = false ∧ safe t :=
    ⟨by simp [Cond.test,ht.counter,(ht.index 17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17],ht.safe⟩
  obtain ⟨t,et,ht⟩ := Block.Eval.loop_invariant_exact I s g (4*width+9) init step stop
  have clock : (4*width+9)+2 = 4*width+11 := by omega
  rw [clock] at et
  exact ⟨t,et,ht.dest,ht.copied,ht.data,ht.index⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
